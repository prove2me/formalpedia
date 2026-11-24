-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_eval_field
-- name    : GlobalTheory.CompanionTheory.SubsetSum.eval_field
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:31.122607+00:00
-- url     : https://prove2.me/theorems/ace74bdd-a669-4fc2-b13a-1bb52cd236e7
-- title:
--   Subset Sum: eval field
-- statement:
--   The Subset Sum construction uses the eval field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L120-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L120-L136

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SubsetSum

theorem GlobalTheory.CompanionTheory.SubsetSum.eval_field {K : Type*} [Field K] [IsAlgClosed K] (r : ℕ) (hr : 0 < r) (P Q : K[X])
    (hP : P.Monic) (hQ : Q.Monic) (hd : P.natDegree = r) :
    ∃ M : Multiset K, Multiset.card M = r + Q.natDegree ∧
      P * Q = (M.map fun x => X + C x).prod ∧ (subsetPoly r M).eval (P.coeff (r - 1)) = 0 := by sorry
