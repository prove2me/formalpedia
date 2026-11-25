-- Prove2me | Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isoLoc_eq_of_hasParamX
-- name    : GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_eq_of_hasParamX
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:36:54.608043+00:00
-- url     : https://prove2.me/theorems/adb0e925-bb45-43f2-bb1d-a80e32e933e4
-- title:
--   Split Place Good Signature: iso Loc eq of has Param X
-- statement:
--   The Split Place Good Signature construction uses the iso Loc eq of has Param X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L52-L59

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

theorem GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_eq_of_hasParamX (hL : ParamLaws N A) {i : N.Loc} (hloc : LocOfPt N A i) {x : N.X i}
    {Sig Sig' : List (Part A.CG)} (h : HasParamX N A i x Sig) (h' : HasParamX N A i x Sig')
    (w : PlE H) (hw : IsSplitPl H w) : isoLoc N A Sig w = isoLoc N A Sig' w := by sorry
