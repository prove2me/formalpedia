-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_13
-- name    : KallMayerSLP.Multistage.eq_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:19:00.670439+00:00
-- url     : https://prove2.me/theorems/748e4432-9172-453a-854a-5cbfdc8e40f0
-- title:
--   (3.12) becomes (3.13) — node probabilities and realizations under independence
-- statement:
--   Let (3.10) satisfy Assumption 3.2, take a scenario tree, and let $n$ be a node of stage $t$ with history $\{\ell_1,\dots,\ell_t=n\}$. Then
--   $$
--   \mathbb P\big(\Omega^{(n)}\big)=\prod_{\nu=2}^{t}\mathbb P_{\xi_\nu}\big(\Xi^\nu_{\ell_\nu}\big)=p_n,
--   $$
--   and, if $p_n>0$, for every $s=2,\dots,t$ the $s$-th component of $\mathbb E[\zeta_t\mid\Omega^{(n)}]$ is $\mathbb E[\xi_s\mid\xi_s\in\Xi^s_{\ell_s}]$, the $s$-th component of $\widehat\zeta^n$.
--
--   This is the passage from the general distribution (3.12) of the discrete process to its product form (3.13), which uses the stochastic independence of $\xi_2,\dots,\xi_T$.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: (3.13) stated for all nodes → the means stated for p_n > 0 only; reason: on a null event the conditional expectation of (3.12) is undefined
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.12)–(3.13), p.262 (PDF 271)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_zetaHat
import Definitions.Def_KallMayerSLP_Multistage_nodeProb
import Definitions.Def_KallMayerSLP_Multistage_omegaNode

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, (3.12) becomes (3.13)** (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, (3.12)–(3.13), p.262, PDF 271): under stochastic independence, the probability of the
event `Ω^(n)` is the product `p_n` of the stagewise probabilities of the history of `n`, and the
conditional expectation of `ζ_{t_n}` given `Ω^(n)`, the realization of (3.12), is the vector `ζ̂^n`
of stagewise conditional means of (3.13).

**Formalization Note.** The conditional expectation given `Ω^(n)` is
`P(Ω^(n))⁻¹ • ∫_{Ω^(n)} ξ_s dP`, stated component by component, and only for `p_n > 0`: on a null
event the book's conditional expectation is undefined. -/
theorem eq_3_13 {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ)
    {t : ℕ} (ht₁ : 1 ≤ t) (ht : t ≤ D.T) (n : 𝒯.Node t) :
    P.real (omegaNode 𝒯 ξ n) = nodeProb 𝒯 P ξ n ∧
      (0 < nodeProb 𝒯 P ξ n → ∀ s : Set.Icc 2 t,
        (P.real (omegaNode 𝒯 ξ n))⁻¹ • ∫ ω in omegaNode 𝒯 ξ n, ξ s ω ∂P = zetaHat 𝒯 P ξ n s) := by sorry

end KallMayerSLP.Multistage
