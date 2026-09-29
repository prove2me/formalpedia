-- Prove2me | Theorems.Thm_Hairer_uniform_grid_model_comparison
-- name    : Hairer.uniform_grid_model_comparison
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T20:54:55.517809+00:00
-- url     : https://prove2.me/theorems/73695f27-e146-4293-9fa7-a3800d4ad385
-- title:
--   Uniform comparison of grid approximations with the model germ
-- statement:
--   Let a regularity structure, a model, and a modelled distribution f of order γ be given. Form Rδ by gluing the germs Π_z f(z) with the explicit smooth anisotropic grid partition of unity of mesh δ. For every compact K there is C ≥ 0, independent of the center x, normalized test η, and scales, such that for x ∈ K and 0 < δ ≤ ρ ≤ 2δ with ρ ≤ 1/2,
--
--   |Rδ(η_x^ρ) − (Π_x f(x))(η_x^ρ)| ≤ C δ^γ.
--
--   Here η ranges over the model’s normalized test ball of order r. The proof localizes η_x^ρ to individual grid cells, applies model-germ coherence, and sums using a relative-volume bound. This auxiliary estimate compares a finite-scale approximation with the local germ; it does not by itself establish the full reconstruction theorem.
-- source:
--   Auxiliary estimate toward M. Hairer, A theory of regularity structures, Theorem 3.10; the explicit smooth grid construction is part of this formalization.

import Definitions.Def_Hairer_Model
open BigOperators Hairer
noncomputable section

theorem Hairer.uniform_grid_model_comparison
    {d : ℕ} {s : Fin d → ℕ} (hs : IsScaling s) {γ : ℝ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (K : Set (Pt d)) (hK : IsCompact K) :
    let W : Pt d → ℝ := fun z ↦
      ∏ i, (Real.smoothTransition (z i + 1) - Real.smoothTransition (z i))
    let X := fun (δ : ℝ) (j : Fin d → ℤ) (i : Fin d) ↦ δ ^ s i * (j i : ℝ)
    let R := fun (δ : ℝ) (φ : Pt d → ℝ) ↦ ∑ᶠ j : Fin d → ℤ,
      (Pi (X δ j) (f (X δ j))).eval
        (fun y ↦ W (fun i ↦ y i / δ ^ s i - (j i : ℝ)) * φ y)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ρ δ : ℝ, 0 < δ → δ ≤ ρ →
      ρ ≤ 2 * δ → ρ ≤ 1 / 2 → ∀ η : Pt d → ℝ, IsTestBall s r η →
      |R δ (scaledTest s ρ x η) - (Pi x (f x)).eval (scaledTest s ρ x η)| ≤
        C * δ ^ γ := by sorry
