-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_esymm_one_eq_sum
-- name    : GlobalTheory.CompanionTheory.SubsetSum.esymm_one_eq_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:32.221935+00:00
-- url     : https://prove2.me/theorems/facb918b-4eeb-45a9-b5b8-5c48431b1c2e
-- title:
--   Subset Sum: esymm one eq sum
-- statement:
--   The Subset Sum construction uses the esymm one eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L117-L118

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

theorem GlobalTheory.CompanionTheory.SubsetSum.esymm_one_eq_sum {R : Type*} [CommRing R] (M : Multiset R) : M.esymm 1 = M.sum := by sorry
