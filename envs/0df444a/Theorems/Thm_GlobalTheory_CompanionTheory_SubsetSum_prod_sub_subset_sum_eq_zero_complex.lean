-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SubsetSum_prod_sub_subset_sum_eq_zero_complex
-- name    : GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:16:22.903147+00:00
-- url     : https://prove2.me/theorems/488905c1-091b-471e-bfcd-638287d1c681
-- title:
--   Subset Sum: prod sub subset sum eq zero complex
-- statement:
--   The Subset Sum construction uses the prod sub subset sum eq zero complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L203-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishes.lean#L203-L215

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

theorem GlobalTheory.CompanionTheory.SubsetSum.prod_sub_subset_sum_eq_zero_complex (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ)
    (m : Multiset ℂ) (A B : R[X]) (hr : 0 < r) (hA : A.Monic) (hB : B.Monic)
    (hd : A.natDegree = r)
    (h : A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod) :
    ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by sorry
