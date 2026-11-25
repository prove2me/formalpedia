-- Prove2me | Theorems.Thm_GlobalTheory_CubNondeg_descend_linComb
-- name    : GlobalTheory.CubNondeg.descend_linComb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:10:02.842859+00:00
-- url     : https://prove2.me/theorems/d8fb5d1e-2844-500a-9ee3-64dea701f80f
-- title:
--   Cub Nondeg: descend lin Comb
-- statement:
--   The Cub Nondeg construction uses the descend lin Comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RatioTranslate.lean#L26-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RatioTranslate.lean#L26-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TorsionInvariantDescendsFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RatioTranslate
import Theorems.Thm_GlobalTheory_UU_IsWt_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CubNondeg

theorem GlobalTheory.CubNondeg.descend_linComb {X Y Y' : Scheme.{0}} (m : Y' ⟶ Y) {T : Type} (τ : T → (Y' ⟶ Y'))
    (hτ : ∀ t, τ t ≫ m = m)
    (H : ∀ (V : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ V)),
      (∀ t, ∀ h : m ⁻¹ᵁ V ≤ τ t ⁻¹ᵁ (m ⁻¹ᵁ V), ((τ t).appLE _ _ h).hom a = a) →
      ∃! a' : Γ(Y, V), (m.app V).hom a' = a)
    (M : LB X) (hM : M.IsLB) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (σ : LB.Gen (LB.LinComb M (fun k => m ≫ ψ k) ε)) (hσ : σ.IsGen)
    (inv : ∀ t (z : Y') (J : (Y' ⟶ X) → M.1), Good M z J → val σ (τ t) z J = val σ (𝟙 Y') z J) :
    ∃ t : (LB.LinComb M ψ ε).Gen, t.IsGen := by sorry
