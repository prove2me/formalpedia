-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_le_one_of_eval_eq_zero
-- name    : GroundTheory.PAdicHodge.norm_le_one_of_eval_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:20.40421+00:00
-- url     : https://prove2.me/theorems/feff8e6c-9ee9-4046-a922-67b91a496685
-- title:
--   PAdic Hodge: norm le one of eval eq zero
-- statement:
--   The PAdic Hodge construction uses the norm le one of eval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L59-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApproxLemmas.lean#L59-L89

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {E : Type*} [NormedField E] [IsUltrametricDist E]

theorem GroundTheory.PAdicHodge.norm_le_one_of_eval_eq_zero {f : E[X]} (hf : f.Monic) (hc : ∀ n, ‖f.coeff n‖ ≤ 1)
    {r : E} (hr : f.eval r = 0) : ‖r‖ ≤ 1 := by sorry
