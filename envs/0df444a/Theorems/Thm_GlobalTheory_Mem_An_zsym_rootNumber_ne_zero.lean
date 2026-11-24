-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_zsym_rootNumber_ne_zero
-- name    : GlobalTheory.Mem.An.zsym_rootNumber_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:41.229593+00:00
-- url     : https://prove2.me/theorems/a6596ba4-ef62-4f2a-b982-bac7380436c4
-- title:
--   An: zsym root Number ne zero
-- statement:
--   The An construction uses the zsym root Number ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean#L25-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean#L25-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DirichletLZeroSymmetry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Complex GlobalTheory.Mem.An
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An
variable {q : ℕ}
variable [NeZero q]

theorem GlobalTheory.Mem.An.zsym_rootNumber_ne_zero {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    χ.rootNumber ≠ 0 := by sorry
