-- Prove2me | Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_goodRow_iff_goodSig
-- name    : GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:36:45.70485+00:00
-- url     : https://prove2.me/theorems/8cda81a0-cbad-4fd5-9753-dab43a31a22c
-- title:
--   Split Place Good Signature: good Row iff good Sig
-- statement:
--   The Split Place Good Signature construction uses the good Row iff good Sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L41-L50

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

theorem GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig {i : N.Loc} {σ : what₂.FT} {Sig : List (Part A.CG)}
    (h : ∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w) :
    N.goodRow σ ↔ goodSig N A Sig := by sorry
