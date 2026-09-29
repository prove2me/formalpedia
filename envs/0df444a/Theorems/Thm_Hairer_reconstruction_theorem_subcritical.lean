-- Prove2me | Theorems.Thm_Hairer_reconstruction_theorem_subcritical
-- name    : Hairer.reconstruction_theorem_subcritical
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T21:50:35.624012+00:00
-- url     : https://prove2.me/theorems/8dbb9f02-f4e6-47a3-8cc0-abd4d70179e0
-- title:
--   Unique reconstruction with all strictly lower negative regularities
-- statement:
--   For a model on a regularity structure with a negative lower bound α on its homogeneities and a modelled distribution of positive regularity γ, there is a single unique reconstruction satisfying the local reconstruction estimate and belonging to C^β for every β < α. This includes integer α with any strictly positive loss of regularity. It does not assert the exact integer endpoint.
-- source:
--   Corollary of the formal reconstruction existence, uniqueness, and model size bounds in the Hairer regularity structures project. Uses the strict gap below the spectral lower bound to compare test-function orders.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.reconstruction_theorem_subcritical
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : α < 0) (hlower : ∀ a ∈ A, α ≤ a)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f) :
    ∃ ξ : Distrib d, (∀ β : ℝ, β < α → MemCalpha s β ξ) ∧
      (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
          |(ξ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) ∧
      (∀ ζ : Distrib d,
        (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) → ζ = ξ) := by sorry
