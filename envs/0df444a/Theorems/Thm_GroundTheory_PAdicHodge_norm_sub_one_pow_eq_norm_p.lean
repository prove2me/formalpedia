-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_pow_eq_norm_p
-- name    : GroundTheory.PAdicHodge.norm_sub_one_pow_eq_norm_p
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:19.711298+00:00
-- url     : https://prove2.me/theorems/4bc700f0-6dda-48ee-89a4-1c8263c02d64
-- title:
--   PAdic Hodge: norm sub one pow eq norm p
-- statement:
--   The PAdic Hodge construction uses the norm sub one pow eq norm p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L43-L53

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

theorem GroundTheory.PAdicHodge.norm_sub_one_pow_eq_norm_p {p : ℕ} [hp : Fact p.Prime] {ζ : F} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ‖ζ - 1‖ ^ (p ^ k * (p - 1)) = ‖(p : F)‖ := by sorry
