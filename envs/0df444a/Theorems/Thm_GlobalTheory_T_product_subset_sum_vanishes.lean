-- Prove2me | Theorems.Thm_GlobalTheory_T_product_subset_sum_vanishes
-- name    : GlobalTheory.T.product_subset_sum_vanishes
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:59.471914+00:00
-- url     : https://prove2.me/theorems/53237a72-b2e4-4af6-9052-65ead547c494
-- title:
--   T: product subset sum vanishes
-- statement:
--   The T construction uses the product subset sum vanishes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishesStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSubsetSumVanishesStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishes
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSubsetSumVanishesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.product_subset_sum_vanishes : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (r : ℕ) (m : Multiset ℂ) (A B : R[X]), 0 < r → A.Monic → B.Monic → A.natDegree = r →
  A * B = (m.map fun x => X + C (algebraMap ℂ R x)).prod →
  ((m.powersetCard r).map fun S => A.coeff (r - 1) - algebraMap ℂ R S.sum).prod = 0 := by sorry
