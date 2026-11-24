-- Prove2me | Theorems.Thm_GlobalTheory_WittGauss_weight_add
-- name    : GlobalTheory.WittGauss.weight_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:11.669675+00:00
-- url     : https://prove2.me/theorems/11ce9738-ef06-4c1e-b8c6-1b56a79e6c6a
-- title:
--   Witt Gauss: weight add
-- statement:
--   The Witt Gauss construction uses the weight add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L97-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormUltrametric.lean#L97-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittGauss
open WittVector
variable {R : Type} [CommRing R] (a : R → ℝ) (hb : ∀ x, 0 ≤ a x ∧ a x ≤ 1) (h0 : a 0 = 0)
  (h1 : a 1 = 1) (hm : ∀ x y, a (x * y) = a x * a y) (ha : ∀ x y, a (x + y) ≤ max (a x) (a y))
include hb h0 h1 hm ha

theorem GlobalTheory.WittGauss.weight_add (p : ℕ) [Fact p.Prime] (c : ℝ) (hc : 0 ≤ c) (x y : WittVector p R)
    (hx : ∀ i, a (x.coeff i) ≤ c ^ p ^ i) (hy : ∀ i, a (y.coeff i) ≤ c ^ p ^ i) (n : ℕ) :
    a ((x + y).coeff n) ≤ c ^ p ^ n := by sorry
