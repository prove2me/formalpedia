-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_not_sq_dvd_choose_pow_pow
-- name    : GroundTheory.PAdicHodge.not_sq_dvd_choose_pow_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:23.055903+00:00
-- url     : https://prove2.me/theorems/755f9b6f-3cf4-4b4b-b32b-87730804254e
-- title:
--   PAdic Hodge: not sq dvd choose pow pow
-- statement:
--   The PAdic Hodge construction uses the not sq dvd choose pow pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L28-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L28-L55

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
noncomputable section

theorem GroundTheory.PAdicHodge.not_sq_dvd_choose_pow_pow {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    ¬ p ^ 2 ∣ Nat.choose (p ^ k) (p ^ (k - 1)) := by sorry
