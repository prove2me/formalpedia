-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_span_p_pow_map
-- name    : GroundTheory.PAdicHodge.ACris.span_p_pow_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:11.815798+00:00
-- url     : https://prove2.me/theorems/c4a453ec-148a-5a78-8ba2-845be512d945
-- title:
--   ACris: span p pow map
-- statement:
--   The ACris construction uses the span p pow map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisBdRInj.lean#L60-L63

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdR
import Definitions.Def_GroundTheory_PAdicHodge_ACrisBdRInj
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.ACris.span_p_pow_map (k : ℕ) :
    (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p)) =
      Ideal.span {(p : ACris K p)} ^ k := by sorry
