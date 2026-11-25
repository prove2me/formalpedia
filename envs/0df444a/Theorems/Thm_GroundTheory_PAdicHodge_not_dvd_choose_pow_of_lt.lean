-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_not_dvd_choose_pow_of_lt
-- name    : GroundTheory.PAdicHodge.not_dvd_choose_pow_of_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:47:17.364284+00:00
-- url     : https://prove2.me/theorems/8fa256a3-643e-4852-bc13-2bb67b82ca74
-- title:
--   PAdic Hodge: not dvd choose pow of lt
-- statement:
--   The PAdic Hodge construction uses the not dvd choose pow of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AxLemma.lean#L11-L26

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

theorem GroundTheory.PAdicHodge.not_dvd_choose_pow_of_lt {p : ℕ} [hp : Fact p.Prime] {d k : ℕ} (h1 : p ^ k ≤ d)
    (h2 : d < p ^ (k + 1)) : ¬ p ∣ Nat.choose d (p ^ k) := by sorry
