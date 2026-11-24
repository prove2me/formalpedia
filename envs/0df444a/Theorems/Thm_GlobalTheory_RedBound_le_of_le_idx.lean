-- Prove2me | Theorems.Thm_GlobalTheory_RedBound_le_of_le_idx
-- name    : GlobalTheory.RedBound.le_of_le_idx
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:18:32.596132+00:00
-- url     : https://prove2.me/theorems/5a4627ff-fbd2-48c1-94a7-5ac562466b2e
-- title:
--   Red Bound: le of le idx
-- statement:
--   The Red Bound construction uses the le of le idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SiegelReducedIntegralFormBoundedEntries.lean#L33-L38

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

theorem GlobalTheory.RedBound.le_of_le_idx {N : ℕ} {C Cm : ℝ} {k : Matrix (Fin N) (Fin N) ℝ} {a : Fin N → ℝ}
    {n : Matrix (Fin N) (Fin N) ℝ} (hS : IsSiegel C k a n) (h1 : 1 ≤ Cm) (hC : C ≤ Cm)
    {i p : Fin N} (h : i ≤ p) : a i ≤ Cm * a p := by sorry
