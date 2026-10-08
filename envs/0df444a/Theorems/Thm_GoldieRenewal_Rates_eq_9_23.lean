-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_eq_9_23
-- name    : GoldieRenewal.Rates.eq_9_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:14:29.038231+00:00
-- url     : https://prove2.me/theorems/3049ed97-5250-4311-aa9a-b4ee5227dc7c
-- title:
--   (9.23), proof of Theorem 3.2 — K ∗ (r(·) − C₊) = K ∗ g₁ ∗ ν₁ + K ∗ g₁ ∗ (p(·) − 1/m)
-- statement:
--   Assume the hypotheses of Theorem 3.2 (with $\eta$ satisfying (3.1) and the subsequent conditions of Theorem 3.1) and (3.7). Let $b>\beta$, $K(t)=be^{-bt}\mathbf 1_{t>0}$ and $r(t)=e^{\kappa t}P(R>e^t)$. Let $\nu=\sum_n\eta^{(n)}=\nu_0+\nu_1$ where $\nu_1$ is finite with $\tilde\nu_1(\beta)<\infty$ and $\nu_0$ has a continuous, bounded, nonnegative density $p$. Then for every $t\in\mathbb R$
--   $$K*(r(\cdot)-C_+)(t)=K*g_1*\nu_1(t)+K*g_1*(p(\cdot)-1/m)(t),$$
--   where $m=\mathbf E M^\kappa\log M$.
--
--   This identity splits the smoothed tail into a part driven by the finite measure $\nu_1$ and a part driven by the renewal density, to which the expansion of Theorem 3.1 applies.
--
--   **Formalization Note** $(f*g)(t)=\int f(t-u)g(u)\,du$, $(f*\nu_1)(t)=\int f(t-u)\,\nu_1(du)$, and $K*g_1*\nu_1$ means $(K*g_1)*\nu_1$. The identity is asserted for every decomposition with the properties that Theorem 3.1 provides. (3.7) is read with $P(R>t)$ in place of the printed $P(R>-t)$.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, §9, proof of Theorem 3.2(i), (9.23), p. 154

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion

open MeasureTheory ProbabilityTheory

namespace GoldieRenewal.Rates

/-- **(9.23)** (Goldie 1991, proof of Theorem 3.2(i), p. 154). Under the hypotheses of
Theorem 3.2 and (3.7), with `K(t) = b e^{−bt} 1_{t>0}` for a constant `b > β`,
`r(t) = e^{κt}P(R > e^t)`, `η = tiltedLaw P M κ` and `ν = Σ η^{(n)} = ν₀ + ν₁` the decomposition
of Theorem 3.1 (`ν₁` finite with `ν̃₁(β) < ∞`, `ν₀` with continuous bounded density `p`):
`K ∗ (r(·) − C₊) = K ∗ g₁ ∗ ν₁ + K ∗ g₁ ∗ (p(·) − 1/m)`.
Formalization Note: function convolutions are `(f ∗ g)(t) = ∫ f(t − u) g(u) du`, and
`(f ∗ ν₁)(t) = ∫ f(t − u) ν₁(du)`; `K ∗ g₁ ∗ ν₁` is read `(K ∗ g₁) ∗ ν₁`. `m = E M^κ log M`
(`mConst`), the mean of `η`. The identity is asserted for every decomposition with the stated
properties (the paper uses the one Theorem 3.1 provides). (3.7) is read with `P(R > t)`. -/
theorem eq_9_23 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M))
    (h_stone : StoneConditions (tiltedLaw P M κ) β)
    (h_3_7 : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1)) (Set.Ioi 0))
    (b : ℝ) (hb : β < b)
    (ν₀ ν₁ : Measure ℝ) (p : ℝ → ℝ)
    (h_dec : renewalMeasure (tiltedLaw P M κ) = ν₀ + ν₁)
    (h_fin : IsFiniteMeasure ν₁) (h_exp1 : expTransform ν₁ β < ⊤)
    (h_dens : ν₀ = volume.withDensity (fun x => ENNReal.ofReal (p x)))
    (hp_nonneg : ∀ x, 0 ≤ p x) (hp_cont : Continuous p) (hp_bdd : ∃ C : ℝ, ∀ x, |p x| ≤ C) :
    ∀ t : ℝ,
      ∫ u : ℝ, smoothingKernel b (t - u) * (GoldieRenewal.Implicit.rFun P R κ u - CPlus P M R κ) =
        (∫ u : ℝ, (∫ v : ℝ, smoothingKernel b (t - u - v) * gPos P M R κ v) ∂ν₁) +
        ∫ u : ℝ, (∫ v : ℝ, smoothingKernel b (t - u - v) * gPos P M R κ v) *
          (p u - 1 / mConst P M κ) := by sorry

end GoldieRenewal.Rates
