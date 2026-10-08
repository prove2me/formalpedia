-- Prove2me | Theorems.Thm_MechanismDesign_Dynamic_optimal_multi_buyer
-- name    : MechanismDesign.Dynamic.optimal_multi_buyer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T06:23:25.066209+00:00
-- url     : https://prove2.me/theorems/2a98f7cc-89c7-4169-8d97-bd91794bdbd4
-- title:
--   Proposition 11.11 -- the optimal sequential mechanism with several buyers
-- statement:
--   Consider sequential mechanism design with a finite set $I$ of independent buyers, and suppose Assumption 11.2 holds: each virtual valuation $\psi_i(\tau_i,\theta_i)$ is increasing in $\tau_i$ and $\theta_i$. Let
--   $$q^*_i(\tau,\theta)=\begin{cases}1&\text{if }\psi_i(\tau_i,\theta_i)>0\text{ and }\psi_i(\tau_i,\theta_i)>\psi_j(\tau_j,\theta_j)\text{ for all }j\ne i,\\0&\text{otherwise.}\end{cases}$$
--
--   1. An admissible, incentive-compatible and individually rational mechanism is optimal if and only if, almost surely,
--   $$\sum_{i\in I}\psi_i(\tau_i,\theta_i)\,q_i(\tau,\theta)=\max\Bigl(0,\max_{i\in I}\psi_i(\tau_i,\theta_i)\Bigr),$$
--   and $U_i(\underline\tau)=0$ for every buyer $i$.
--   2. If ties $\psi_i(\tau_i,\theta_i)=\psi_j(\tau_j,\theta_j)$, $i\ne j$, have probability zero, an optimal mechanism with allocation rule $q^*$ exists. If moreover $\psi_i(\tau_i,\theta_i)=0$ has probability zero for every $i$, an admissible, incentive-compatible and individually rational mechanism is optimal if and only if (i) $q=q^*$ almost surely, and (ii) for all $i$ and all $(\tau_i,\theta_i)$
--   $$T_i(\tau_i,\theta_i)=T_{i0}(\tau_i)+\theta_iQ_i(\tau_i,\theta_i)-\int_{\underline\theta}^{\theta_i}Q_i(\tau_i,x)\,dx,$$
--   with $T_{i0}$ given by Proposition 11.5 for $(Q_i,T_i)$ and $T_i(\underline\tau,\underline\theta)$ pinned down by $U_i(\underline\tau)=0$.
--
--   The optimal mechanism gives the good to the buyer with the highest positive virtual valuation; with a separable informativeness measure it is implemented by a handicap auction.
--
--   **Formalization Note** The page states (i)–(ii) "for all $(\tau,\theta)\in T\times\Theta$". The allocation rule it displays gives the good to nobody when two positive virtual valuations tie, which is not revenue-maximizing when ties have positive probability, and the values of $q$ on a null set or where $\psi_i=0$ do not affect revenue. Item 1 is the characterization that holds in general, and item 2 restates the page's characterization under the conditions that make it true. In the page's formula for $T_{i0}$ the density $f_i(\hat\theta\mid\tau)$ is read as $f_i(\hat\theta\mid\tau_i)$. Probability refers to the joint law of the type profile.
-- source:
--   Krähmer & Strausz, Ch. 11 in Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.226–227, Proposition 11.11

import Mathlib
import Definitions.Def_MechanismDesign_Dynamic_Model
import Definitions.Def_MechanismDesign_Dynamic_OptimalScreening
import Definitions.Def_MechanismDesign_Dynamic_MultiBuyer

open MeasureTheory

namespace MechanismDesign.Dynamic

/-- **Proposition 11.11**, pp.226–227. Suppose Assumption 11.2 holds. Write `ψᵢ` for buyer `i`'s
virtual valuation and `q*` for the rule (i): `q*ᵢ(τ, θ) = 1` if `ψᵢ(τᵢ, θᵢ) > 0` and
`ψᵢ(τᵢ, θᵢ) > ψⱼ(τⱼ, θⱼ)` for all `j ≠ i`, `0` otherwise.

1. An admissible, incentive-compatible, individually rational mechanism is optimal if and only if
   almost surely `∑ᵢ ψᵢ(τᵢ, θᵢ) qᵢ(τ, θ) = max(0, maxᵢ ψᵢ(τᵢ, θᵢ))`, and `Uᵢ(τ̲) = 0` for all `i`.
2. If ties `ψᵢ(τᵢ, θᵢ) = ψⱼ(τⱼ, θⱼ)` (`i ≠ j`) have probability zero, then an optimal mechanism
   with allocation rule `q*` exists; if moreover `ψᵢ(τᵢ, θᵢ) = 0` has probability zero for every
   `i`, an admissible, incentive-compatible, individually rational mechanism is optimal if and
   only if (i) `q = q*` almost surely, and (ii) for all `i` and all `(τᵢ, θᵢ)`,
   `Tᵢ(τᵢ, θᵢ) = Tᵢ₀(τᵢ) + θᵢ Qᵢ(τᵢ, θᵢ) − ∫_{θ̲}^{θᵢ} Qᵢ(τᵢ, x) dx`, with `Tᵢ₀` as in
   Proposition 11.5 for `(Qᵢ, Tᵢ)`, and `Tᵢ(τ̲, θ̲)` pinned down by `Uᵢ(τ̲) = 0`.

The page states (i)–(ii) "for all `(τ, θ) ∈ T × Θ`" without the tie conditions; item 1 is the
characterization that holds in general. -/
theorem optimal_multi_buyer {τlo τhi θlo θhi : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → SeqEnv τlo τhi θlo θhi) (hA : Assumption11_2 E) :
    (∀ m : MultiMechanism ι τlo τhi θlo θhi, m.Admissible E → m.IsIC E → m.IsIR E →
      (m.IsOptimal E ↔
        (∀ᵐ x ∂profileLaw E, ∑ i, (E i).ψ (x i).1 (x i).2 * m.q x i =
            max 0 (⨆ i, (E i).ψ (x i).1 (x i).2)) ∧
          ∀ i, (m.interim E i).U (E i) τlo = 0)) ∧
    ((∀ i j, i ≠ j →
        profileLaw E {x | (E i).ψ (x i).1 (x i).2 = (E j).ψ (x j).1 (x j).2} = 0) →
      (∃ m : MultiMechanism ι τlo τhi θlo θhi, m.Admissible E ∧
        (∀ x ∈ profileRect ι τlo τhi θlo θhi, ∀ i, m.q x i = optAlloc E x i) ∧
        m.IsOptimal E) ∧
      ((∀ i, profileLaw E {x | (E i).ψ (x i).1 (x i).2 = 0} = 0) →
        ∀ m : MultiMechanism ι τlo τhi θlo θhi, m.Admissible E → m.IsIC E → m.IsIR E →
          (m.IsOptimal E ↔
            (∀ᵐ x ∂profileLaw E, ∀ i, m.q x i = optAlloc E x i) ∧
              ∀ i,
                (∀ τi ∈ Set.Icc τlo τhi, ∀ θi ∈ Set.Icc θlo θhi,
                  m.interimT E i τi θi =
                    (E i).t0 (m.interimQ E i) (m.interimT E i τlo θlo) τi +
                      θi * m.interimQ E i τi θi - ∫ x in θlo..θi, m.interimQ E i τi x) ∧
                (m.interim E i).U (E i) τlo = 0))) := by sorry

end MechanismDesign.Dynamic
