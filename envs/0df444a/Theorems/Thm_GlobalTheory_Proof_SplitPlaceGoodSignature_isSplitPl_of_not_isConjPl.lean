-- Prove2me | Theorems.Thm_GlobalTheory_Proof_SplitPlaceGoodSignature_isSplitPl_of_not_isConjPl
-- name    : GlobalTheory.Proof.SplitPlaceGoodSignature.isSplitPl_of_not_isConjPl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:37:19.495922+00:00
-- url     : https://prove2.me/theorems/878b19c6-be76-4241-adcb-c811f2355288
-- title:
--   Split Place Good Signature: is Split Pl of not is Conj Pl
-- statement:
--   The Split Place Good Signature construction uses the is Split Pl of not is Conj Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/SplitPlaceGoodSignature.lean#L14-L28

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

theorem GlobalTheory.Proof.SplitPlaceGoodSignature.isSplitPl_of_not_isConjPl (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H.E))
    (h : ¬ IsConjPl H w w) : IsSplitPl H w := by sorry
