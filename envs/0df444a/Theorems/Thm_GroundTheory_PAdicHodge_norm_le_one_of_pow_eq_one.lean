-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_le_one_of_pow_eq_one
-- name    : GroundTheory.PAdicHodge.norm_le_one_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:13.17952+00:00
-- url     : https://prove2.me/theorems/6fe578c5-e122-42e5-832c-0989f1b3a0d1
-- title:
--   PAdic Hodge: norm le one of pow eq one
-- statement:
--   The PAdic Hodge construction uses the norm le one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
omit [IsUltrametricDist F]

theorem GroundTheory.PAdicHodge.norm_le_one_of_pow_eq_one {ζ : F} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : ‖ζ‖ ≤ 1 := by sorry
