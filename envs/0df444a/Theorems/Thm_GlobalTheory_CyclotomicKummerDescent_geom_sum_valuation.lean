-- Prove2me | Theorems.Thm_GlobalTheory_CyclotomicKummerDescent_geom_sum_valuation
-- name    : GlobalTheory.CyclotomicKummerDescent.geom_sum_valuation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:41.656642+00:00
-- url     : https://prove2.me/theorems/e27a6c2c-8c90-49df-9396-50629100d5a6
-- title:
--   Cyclotomic Kummer Descent: geom sum valuation
-- statement:
--   The Cyclotomic Kummer Descent construction uses the geom sum valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowDescentCyclotomic.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowDescentCyclotomic.lean#L8-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowDescentCyclotomic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open GlobalTheory.CyclotomicKummerDescent

theorem GlobalTheory.CyclotomicKummerDescent.geom_sum_valuation {l : ℕ} (hl : l.Prime) {t : ℕ} (ht1 : 1 < t)
    (ht : (l : ℤ) ^ 2 ∣ (t : ℤ) - 1) (r : ℕ) :
    l ^ r ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i ∧
      ¬ l ^ (r + 1) ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i := by sorry
