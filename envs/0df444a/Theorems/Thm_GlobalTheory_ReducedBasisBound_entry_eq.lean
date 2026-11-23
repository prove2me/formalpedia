-- Prove2me | Theorems.Thm_GlobalTheory_ReducedBasisBound_entry_eq
-- name    : GlobalTheory.ReducedBasisBound.entry_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:53.347528+00:00
-- url     : https://prove2.me/theorems/fc23a117-3626-423f-b873-321d32b0824b
-- title:
--   Reduced Basis Bound: entry eq
-- statement:
--   The Reduced Basis Bound construction uses the entry eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBounded.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ReducedBasisIntegralConjEntriesBounded.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UnipotentUpperInvUpperTriangularBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ReducedBasisIntegralConjEntriesBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open GlobalTheory GlobalTheory.ReducedBasisBound

theorem GlobalTheory.ReducedBasisBound.entry_eq {N : ℕ} (a : Fin N → ℝ) (n Z P : Matrix (Fin N) (Fin N) ℝ)
    (h : diagonal a * n * P = Z * diagonal a * n) (p j : Fin N) :
    a p * (n * P) p j = ∑ q, Z p q * a q * n q j := by sorry
