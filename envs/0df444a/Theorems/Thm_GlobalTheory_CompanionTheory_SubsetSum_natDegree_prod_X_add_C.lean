-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_natDegree_prod_X_add_C
-- name    : GlobalTheory.CompanionTheory.SubsetSum.natDegree_prod_X_add_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:44.390222+00:00
-- url     : https://prove2.me/theorems/61661230-5b9a-4497-b757-a9ee2836bd64
-- title:
--   Subset Sum: nat Degree prod X add C
-- statement:
--   The Subset Sum construction uses the nat Degree prod X add C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L97-L105

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

theorem GlobalTheory.CompanionTheory.SubsetSum.natDegree_prod_X_add_C {R : Type*} [CommRing R] [Nontrivial R] (M : Multiset R) :
    ((M.map fun x => X + C x).prod).natDegree = Multiset.card M := by sorry
