-- Prove2me | Theorems.Thm_Hairer_modelled_sector_pi_bound
-- name    : Hairer.modelled_sector_pi_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:43:22.284176+00:00
-- url     : https://prove2.me/theorems/9f0d40f6-88a2-42a4-ab9d-df731fa46eeb
-- title:
--   Local model bound on a sector-valued modelled distribution
-- statement:
--   Suppose a modelled distribution of positive order takes values in a sector of regularity β. On every compact set, applying the model at x to f(x) and testing at scale δ in (0,1] has absolute value at most C δ^β, uniformly over normalized test functions at the model’s test order. The constant exists because only finitely many homogeneous components below the modelled order can contribute. This is the model-term estimate toward sector regularity; it does not assert transfer to a different test order.
-- source:
--   Auxiliary estimate for the sector-regularity argument in M. Hairer, A theory of regularity structures (2014), Corollary 3.16.

import Definitions.Def_Hairer_Model

set_option autoImplicit false
open scoped Classical DirectSum
open BigOperators
noncomputable section

namespace Hairer

theorem modelled_sector_pi_bound
    {d : ℕ} {s : Fin d → ℕ}
    {A : Set ℝ} {E : A → Type} [∀ a : A, NormedAddCommGroup (E a)]
    [∀ a : A, NormedSpace ℝ (E a)]
    {G : Subgroup (ModelSpace A E ≃ₗ[ℝ] ModelSpace A E)} {one : ModelSpace A E}
    (hT : IsRegularityStructure A E G one)
    {r : ℕ} {Pi : Pt d → ModelSpace A E →ₗ[ℝ] Distrib d}
    {Gam : Pt d → Pt d → ModelSpace A E ≃ₗ[ℝ] ModelSpace A E}
    (hmod : IsModel s r G Pi Gam)
    {V : ∀ a : A, Submodule ℝ (E a)} {β γ : ℝ}
    (hV : IsSector G V β) (hγ : 0 < γ)
    {f : Pt d → ModelSpace A E} (hf : IsModelled s γ Gam f)
    (hfV : TakesValuesIn V f) :
    ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K,
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ η : Pt d → ℝ, IsTestBall s r η →
        |(Pi x (f x)).eval (scaledTest s δ x η)| ≤ C * δ ^ β := by sorry

end Hairer
