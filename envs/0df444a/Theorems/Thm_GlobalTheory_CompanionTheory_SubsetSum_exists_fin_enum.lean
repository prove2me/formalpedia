-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_exists_fin_enum
-- name    : GlobalTheory.CompanionTheory.SubsetSum.exists_fin_enum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:37.513944+00:00
-- url     : https://prove2.me/theorems/91f33287-40a4-4c52-a6ed-62391fda8028
-- title:
--   Subset Sum: exists fin enum
-- statement:
--   The Subset Sum construction uses the exists fin enum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L35-L42

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

theorem GlobalTheory.CompanionTheory.SubsetSum.exists_fin_enum {R : Type*} (M : Multiset R) (n : ℕ) (h : Multiset.card M = n) :
    ∃ x : Fin n → R, Finset.univ.val.map x = M := by sorry
