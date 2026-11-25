-- Prove2me | Theorems.Thm_GlobalTheory_NodalCubic_exists_fromLocus
-- name    : GlobalTheory.NodalCubic.exists_fromLocus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:07.436329+00:00
-- url     : https://prove2.me/theorems/fbe2d0d7-2da6-4821-b2b8-49039cb6bcf9
-- title:
--   Nodal Cubic: exists from Locus
-- statement:
--   The Nodal Cubic construction uses the exists from Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RangeSubsetOfForallField.lean#L202-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/RangeSubsetOfForallField.lean#L202-L251

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RangeSubsetOfForallField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NodalCubic
open GlobalTheory.WeierstrassCurve
variable (K : Type) [Field K]
variable {K}
variable (U : (scheme (node K)).Opens)
  (hU : ∀ (k : Type) [Field k] (ρ : K →+* k) (P : Fin 3 → k)
    (h : IsUnimodularSol ((node K).map ρ) P),
    ⊤ ≤ ptHom (node K) ρ P h ⁻¹ᵁ U ↔ ((node K).map ρ).toProjective.Nonsingular P)
include hU

theorem GlobalTheory.NodalCubic.exists_fromLocus : ∃ g : Over.mk (U.ι ≫ toSpec (node K)) ⟶ splitTorus (Spec (.of K)) ℤ,
    ∀ (k : Type) [Field k] (ρ : K →+* k)
      (y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ Over.mk (U.ι ≫ toSpec (node K)))
      (P : Fin 3 → k) (h : IsUnimodularSol ((node K).map ρ) P),
      y.left ≫ U.ι = ptHom (node K) ρ P h → (valOf (y ≫ g) : k) = P 1 / (P 0 + P 1) := by sorry
