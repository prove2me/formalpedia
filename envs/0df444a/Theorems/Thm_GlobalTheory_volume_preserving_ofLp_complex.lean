-- Prove2me | Theorems.Thm_GlobalTheory_volume_preserving_ofLp_complex
-- name    : GlobalTheory.volume_preserving_ofLp_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:11.798901+00:00
-- url     : https://prove2.me/theorems/f48b7f1b-1f97-4418-bffc-1861d2ee5318
-- title:
--   Global Theory: volume preserving of Lp complex
-- statement:
--   The Global Theory construction uses the volume preserving of Lp complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableMonomialMulConjComplexGaussian.lean#L71-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegrableMonomialMulConjComplexGaussian.lean#L71-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped Nat ComplexConjugate
open GlobalTheory

theorem GlobalTheory.volume_preserving_ofLp_complex (ι : Type*) [Fintype ι] :
    MeasurePreserving (@WithLp.ofLp 2 (ι → ℂ)) := by sorry
