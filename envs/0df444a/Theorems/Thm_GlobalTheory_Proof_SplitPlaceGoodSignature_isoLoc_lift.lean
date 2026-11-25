-- Prove2me | Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isoLoc_lift
-- name    : GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:20.780035+00:00
-- url     : https://prove2.me/theorems/33407f6d-50b1-408c-b616-f52cdf391c59
-- title:
--   Split Place Good Signature: iso Loc lift
-- statement:
--   The Split Place Good Signature construction uses the iso Loc lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L35-L39

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

theorem GlobalTheory.Proof.SplitPlaceGoodSignature.isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by sorry
