-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_biInvariant_leadMinor
-- name    : GlobalTheory.UnipotentInvariant.biInvariant_leadMinor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:39.133927+00:00
-- url     : https://prove2.me/theorems/54fb925d-795d-47b0-9a76-1165f53e4d98
-- title:
--   Unipotent Invariant: bi Invariant lead Minor
-- statement:
--   The Unipotent Invariant construction uses the bi Invariant lead Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L62-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}

theorem GlobalTheory.UnipotentInvariant.biInvariant_leadMinor (i : Fin p) : BiInvariant (K := K) (leadMinor i) := by sorry
