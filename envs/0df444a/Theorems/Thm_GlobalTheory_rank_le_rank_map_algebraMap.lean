-- Prove2me | Theorems.Thm_GlobalTheory_rank_le_rank_map_algebraMap
-- name    : GlobalTheory.rank_le_rank_map_algebraMap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:15:24.184927+00:00
-- url     : https://prove2.me/theorems/abae8936-f54f-42f6-b4af-03efa7de6e00
-- title:
--   Global Theory: rank le rank map algebra Map
-- statement:
--   The Global Theory construction uses the rank le rank map algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExt.lean#L35-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankKerMapLeOfFirstOrderKernelExt.lean#L35-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankKerMapLeOfFirstOrderKernelExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.rank_le_rank_map_algebraMap (k K : Type) [Field k] [Field K] [Algebra k K] (a : ℕ)
    (Φ : Matrix (Fin a) (Fin a) k) : Φ.rank ≤ (Φ.map (algebraMap k K)).rank := by sorry
