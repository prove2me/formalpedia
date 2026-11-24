-- Prove2me | Theorems.Thm_GlobalTheory_CompleteDVR_ne_top_of_isDiscreteValuationRing
-- name    : GlobalTheory.CompleteDVR.ne_top_of_isDiscreteValuationRing
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:39.107905+00:00
-- url     : https://prove2.me/theorems/bba87277-a974-4eb2-8f74-0d95f2ba28b3
-- title:
--   Complete DVR: ne top of is Discrete Valuation Ring
-- statement:
--   The Complete DVR construction uses the ne top of is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtension.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteDvrExtension.lean#L30-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum
open GlobalTheory GlobalTheory.CompleteDVR

theorem GlobalTheory.CompleteDVR.ne_top_of_isDiscreteValuationRing {K : Type} [Field K] (V : ValuationSubring K)
    [IsDiscreteValuationRing V] : V ≠ ⊤ := by sorry
