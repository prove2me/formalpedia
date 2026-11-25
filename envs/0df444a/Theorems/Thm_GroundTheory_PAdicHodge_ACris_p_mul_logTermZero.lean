-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_p_mul_logTermZero
-- name    : GroundTheory.PAdicHodge.ACris.p_mul_logTermZero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:23.907702+00:00
-- url     : https://prove2.me/theorems/9667b438-d5dc-4225-8329-ec0dc7846c2d
-- title:
--   ACris: p mul log Term Zero
-- statement:
--   The ACris construction uses the p mul log Term Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L145-L150

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {x : AInf K p}

theorem GroundTheory.PAdicHodge.ACris.p_mul_logTermZero (hx : x ∈ RingHom.ker θ) (j : ℕ) :
    (p : ACrisZero K p) * logTermZero hx j =
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by sorry
