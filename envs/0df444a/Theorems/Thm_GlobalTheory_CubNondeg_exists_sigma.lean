-- Prove2me | Theorems.Thm_GlobalTheory_CubNondeg_exists_sigma
-- name    : GlobalTheory.CubNondeg.exists_sigma
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:19:14.633182+00:00
-- url     : https://prove2.me/theorems/9f6d0d89-4fb1-592a-9c0a-c17efd83e581
-- title:
--   Cub Nondeg: exists sigma
-- statement:
--   The Cub Nondeg construction uses the exists sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RatioTranslate.lean#L101-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RatioTranslate.lean#L101-L117

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
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)

theorem GlobalTheory.CubNondeg.exists_sigma {T : Over S} (n : ℕ) (a x : T ⟶ A) (hx : x ^ n = 1) (φ : Fin 4 → (T.left ⟶ A.left))
    (hφ : φ = ![(a ^ n * x).left, (a ^ n).left, x.left, (1 : T ⟶ A).left]) :
    ∃ σ : LB.Gen (LB.LinComb L.L φ ![1, -1, -1, 1]), σ.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good L.L z J → val σ ρ.left z J =
        cubN (cubV c z J) n 1 (ρ ≫ a) (ρ ≫ x) * (cubN (cubV c z J) n 1 (ρ ≫ x) (ρ ≫ a))⁻¹ := by sorry
