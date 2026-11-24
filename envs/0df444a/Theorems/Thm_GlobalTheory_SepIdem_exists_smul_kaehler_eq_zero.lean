-- Prove2me | Theorems.Thm_GlobalTheory_SepIdem_exists_smul_kaehler_eq_zero
-- name    : GlobalTheory.SepIdem.exists_smul_kaehler_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:53:24.483669+00:00
-- url     : https://prove2.me/theorems/bb60acc4-50bb-4a36-a6c1-b46ee7811aa0
-- title:
--   Sep Idem: exists smul kaehler eq zero
-- statement:
--   The Sep Idem construction uses the exists smul kaehler eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean#L19-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormallyUnramifiedOfIsReduced.lean#L19-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormallyUnramifiedOfIsReduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct nonZeroDivisors
open GlobalTheory GlobalTheory.SepIdem

theorem GlobalTheory.SepIdem.exists_smul_kaehler_eq_zero (O : Type) [CommRing O] [Module.Finite ℤ O] [IsReduced O] :
    ∃ N : ℕ, 0 < N ∧ ∀ ω : Ω[O⁄ℤ], (N : O) • ω = 0 := by sorry
