-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateCompare_dualBC_tangentPt
-- name    : GlobalTheory.HodgeTateCompare.dualBC_tangentPt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:01.276562+00:00
-- url     : https://prove2.me/theorems/db65af49-050d-584c-afc0-96bf875153b5
-- title:
--   Hodge Tate Compare: dual BC tangent Pt
-- statement:
--   The Hodge Tate Compare construction uses the dual BC tangent Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CotangentBidualToTangentFunctionInjective.lean#L372-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CotangentBidualToTangentFunctionInjective.lean#L372-L380

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CotangentBidualToTangentFunctionInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateCompare
open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
noncomputable section
variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem GlobalTheory.HodgeTateCompare.dualBC_tangentPt {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (v : Cotangent G →ₗ[O] R) :
    ptMap (dualBC φ) ≫ (tangentPt v : specO O (DualNumber R) ⟶ G) =
      tangentPt (φ.toLinearMap ∘ₗ v) := by sorry
