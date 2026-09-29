-- Prove2me | Theorems.Thm_Hairer_reconstruction_linear_operator_subcritical
-- name    : Hairer.reconstruction_linear_operator_subcritical
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T22:13:59.880717+00:00
-- url     : https://prove2.me/theorems/a1a41dd4-772a-4688-b9cd-d36f59a53157
-- title:
--   Linear reconstruction operator with all subcritical regularities
-- statement:
--   For a fixed regularity structure and model, positive modelled regularity gamma, and a negative lower bound alpha on the homogeneities, there is a reconstruction map that is additive and real homogeneous on modelled distributions. Each reconstruction belongs to every regularity class beta < alpha and satisfies the reconstruction estimate. The estimate determines it uniquely. This statement does not assert exact regularity at the negative-integer endpoint or continuity of the operator.
-- source:
--   Consequence of Hairer reconstruction existence and uniqueness and the verified subcritical regularity theorem.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.reconstruction_linear_operator_subcritical
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ} (hγ : 0 < γ)
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {α : ℝ} (hα : α < 0) (hlower : ∀ a ∈ A, α ≤ a) :
    ∃ R : (Pt d → ModelSpace A E) → Distrib d,
      (∀ f g : Pt d → ModelSpace A E, IsModelled s γ Gam f → IsModelled s γ Gam g →
        R (f + g) = R f + R g) ∧
      (∀ (c : ℝ) (f : Pt d → ModelSpace A E), IsModelled s γ Gam f →
        R (c • f) = c • R f) ∧
      (∀ f : Pt d → ModelSpace A E, IsModelled s γ Gam f →
        (∀ β : ℝ, β < α → MemCalpha s β (R f)) ∧
        (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
            |(R f - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) ∧
        (∀ ζ : Distrib d,
          (∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
            ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
              |(ζ - Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ γ) → ζ = R f)) := by sorry
