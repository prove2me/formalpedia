-- Prove2me | Theorems.Thm_HuImkellerMuller_Power_bsde_15_unique
-- name    : HuImkellerMuller.Power.bsde_15_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:33.597341+00:00
-- url     : https://prove2.me/theorems/fce420b4-dbec-4e4b-835f-fb2e567f4814
-- title:
--   Proof of Theorem 14, p. 18 — two solutions of (15) in ℋ^∞(ℝ) × ℋ²(ℝ^m) coincide
-- statement:
--   In the setting of Theorem 14, let $(Y^1,Z^1)$ and $(Y^2,Z^2)$ in $\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$ both solve the BSDE (15). Then
--   $$
--   Y^1_t=Y^2_t\ \ P\text{-a.s. for every }t\in[0,T],\qquad Z^1=Z^2\ \ \lambda\otimes P\text{-a.e.}
--   $$
--
--   The paper derives uniqueness from the comparison argument of the uniqueness part of the proof of Theorem 7.
--
--   **Formalization Note** "Unique solution" is read as uniqueness of $Y$ up to modification and of $Z$ up to $\lambda\otimes P$-null sets. $\tilde C\neq\emptyset$ is added.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, proof of Theorem 14, p. 18, first paragraph

import Mathlib
import Definitions.Def_HuImkellerMuller_Power_Strategy
import Definitions.Def_HuImkellerMuller_Power_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Power

/-- Proof of Theorem 14, p. 18: two solutions of (15) in `ℋ^∞(ℝ) × ℋ²(ℝᵐ)` coincide:
`Y¹_t = Y²_t` a.s. for every `t ≤ T`, and `Z¹ = Z²` `λ ⊗ P`-a.e. -/
theorem bsde_15_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d m : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)} (hW : EthierKurtz.IsStandardBrownian P W)
    {𝓕 : Filtration ℝ≥0 mΩ}
    (h𝓕 : CvitanicKaratzas92.Optimality.IsAugmentedBrownianFiltration P W 𝓕)
    {I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ}
    (hI : CvitanicKaratzas92.Optimality.IsItoIntegralOperator P 𝓕 T W I)
    {b : ℝ≥0 → Ω → (Fin d → ℝ)} {σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ}
    (hmkt : MarketHyp P 𝓕 T b σ)
    {Ct : Set (Fin d → ℝ)} (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (Y₁ Y₂ : ℝ≥0 → Ω → ℝ) (Z₁ Z₂ : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m))
    (h₁ : IsSolution15 P 𝓕 T I b σ Ct γ Y₁ Z₁) (h₂ : IsSolution15 P 𝓕 T I b σ Ct γ Y₂ Z₂) :
    (∀ t ≤ T, Y₁ t =ᵐ[P] Y₂ t) ∧
      ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
        Z₁ q.1.toNNReal q.2 = Z₂ q.1.toNNReal q.2 := by sorry

end HuImkellerMuller.Power
