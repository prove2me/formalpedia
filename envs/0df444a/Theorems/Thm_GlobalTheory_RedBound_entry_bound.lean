-- Prove2me | Theorems.Thm_GlobalTheory_RedBound_entry_bound
-- name    : GlobalTheory.RedBound.entry_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:10:21.509394+00:00
-- url     : https://prove2.me/theorems/00298161-8cab-4833-86d3-a8e9f582ab7a
-- title:
--   Red Bound: entry bound
-- statement:
--   The Red Bound construction uses the entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBoundedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SiegelReducedIntegralFormBoundedEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.RedBound

theorem GlobalTheory.RedBound.entry_bound {N : ℕ} (P Z Q : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (c : ℝ)
    (h : ∀ p q, |P i p * Z p q * Q q j| ≤ c) : |(P * Z * Q) i j| ≤ N * N * c := by sorry
