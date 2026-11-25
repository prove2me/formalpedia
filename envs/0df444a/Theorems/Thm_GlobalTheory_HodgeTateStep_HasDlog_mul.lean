-- Prove2me | Theorems.Thm_GlobalTheory_HodgeTateStep_HasDlog_mul
-- name    : GlobalTheory.HodgeTateStep.HasDlog.mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:48.121245+00:00
-- url     : https://prove2.me/theorems/4960f088-f968-5b66-a660-6cd87bec005e
-- title:
--   Has Dlog: mul
-- statement:
--   The Has Dlog construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCharactersDlogMinorsGe.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCharactersDlogMinorsGe.lean#L52-L60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.HodgeTateStep
variable {O : Type} [CommRing O]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

theorem GlobalTheory.HodgeTateStep.HasDlog.mul {p : ℕ} {L : Type} {e : L → LieG G}
    {κ κ' : torsion G (p ^ 1) ⟶ Gm (Spec (CommRingCat.of O))} {y y' : L → O}
    (h : HasDlog p e κ y) (h' : HasDlog p e κ' y') : HasDlog p e (κ * κ') (y + y') := by sorry
