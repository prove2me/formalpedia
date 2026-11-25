-- Prove2me | Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_goodPart_of_lifts
-- name    : GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:17:06.411051+00:00
-- url     : https://prove2.me/theorems/be20f70c-5ac1-5e8a-8deb-bb40385949a5
-- title:
--   Split Place Good Signature: good Part of lifts
-- statement:
--   The Split Place Good Signature construction uses the good Part of lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L61-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L61-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_ThetaLiftOfEachRow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_HeckeSplitOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_SplitLiftOfLiftParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_SplitPlaceGoodSignature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.SplitPlaceGoodSignature
open NumberField Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
variable (N : NData R H what₂) (A : NAut N)

theorem GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts (i : N.Loc) (h1 : ThetaOne N A) (hL : ParamLaws N A)
    (hlift : LiftParam N A i) (hpt : PtLocal N A i) (hloc : LocOfPt N A i) : GoodPart N A i := by sorry
