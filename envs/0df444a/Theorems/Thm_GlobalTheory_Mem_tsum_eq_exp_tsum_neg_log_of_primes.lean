-- Prove2me | Theorems.Thm_GlobalTheory_Mem_tsum_eq_exp_tsum_neg_log_of_primes
-- name    : GlobalTheory.Mem.tsum_eq_exp_tsum_neg_log_of_primes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:56.514305+00:00
-- url     : https://prove2.me/theorems/5b09b44a-e70a-4b07-ae24-f02ab798ef10
-- title:
--   Mem: tsum eq exp tsum neg log of primes
-- statement:
--   The Mem construction uses the tsum eq exp tsum neg log of primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L9-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayLSeriesEulerProduct.lean#L9-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem

theorem GlobalTheory.Mem.tsum_eq_exp_tsum_neg_log_of_primes {α ι : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (p : ι → α) (hp : ∀ i, Prime (p i)) (hdvd : ∀ i j, p i ∣ p j → i = j)
    (f : α → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (h1 : f 1 = 1)
    (hex : ∀ a, a ≠ 1 → f a ≠ 0 → ∃ i, p i ∣ a) (hsum : Summable fun a => ‖f a‖)
    (hne : ∀ i, 1 - f (p i) ≠ 0) :
    ∑' a, f a = exp (∑' i, -log (1 - f (p i))) := by sorry
