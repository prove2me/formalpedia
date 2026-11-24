-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_zsymFactor_analyticAt
-- name    : GlobalTheory.Mem.An.zsymFactor_analyticAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:21:38.410061+00:00
-- url     : https://prove2.me/theorems/ccbd31b2-9ada-4fcb-afcb-4433a253aad7
-- title:
--   An: zsym Factor analytic At
-- statement:
--   The An construction uses the zsym Factor analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean#L60-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DirichletLZeroSymmetry.lean#L60-L69

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

theorem GlobalTheory.Mem.An.zsymFactor_analyticAt (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : s.re < 1) : AnalyticAt ℂ (zsymFactor χ) s := by sorry
