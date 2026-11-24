-- Prove2me | Theorems.Thm_GlobalTheory_SW_ThetaProd_hasLevel_mul
-- name    : GlobalTheory.SW.ThetaProd.hasLevel_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:43:57.351525+00:00
-- url     : https://prove2.me/theorems/7c9d2196-0dbb-404c-a608-3e2390ab29f1
-- title:
--   Theta Prod: has Level mul
-- statement:
--   The Theta Prod construction uses the has Level mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean#L10-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ThetaProd

theorem GlobalTheory.SW.ThetaProd.hasLevel_mul {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (S : ℕ)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : HasLevel (S * R) φ := by sorry
