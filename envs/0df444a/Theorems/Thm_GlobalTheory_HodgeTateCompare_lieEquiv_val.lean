-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateCompare_lieEquiv_val
-- name    : GlobalTheory.HodgeTateCompare.lieEquiv_val
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:08:28.351394+00:00
-- url     : https://prove2.me/theorems/7c0659a0-cad6-58dc-a01b-97f97faf798f
-- title:
--   Hodge Tate Compare: lie Equiv val
-- statement:
--   The Hodge Tate Compare construction uses the lie Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CotangentBidualToTangentFunctionInjective.lean#L129-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CotangentBidualToTangentFunctionInjective.lean#L129-L129

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
variable {O : Type} [CommRing O] [IsLocalRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
variable {G}

theorem GlobalTheory.HodgeTateCompare.lieEquiv_val (v : Lie G) : (lieEquiv G v).1 = tangentPt v := by sorry
