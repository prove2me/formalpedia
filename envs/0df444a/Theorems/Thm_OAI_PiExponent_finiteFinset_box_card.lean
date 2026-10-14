-- Prove2me | Theorems.Thm_OAI_PiExponent_finiteFinset_box_card
-- name    : OAI.PiExponent.finiteFinset_box_card
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T16:19:28.534365+00:00
-- url     : https://prove2.me/theorems/5ec49843-bc83-41d9-adb5-1850a84bc83e
-- title:
--   Cardinality bound for a finite coordinate box
-- statement:
--   A finite set of finitely supported natural-valued functions on `Fin m`, whose coordinates are all below `N`, has cardinality at most `N ^ m`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L35-L47

import Mathlib.Tactic

theorem OAI.PiExponent.finiteFinset_box_card {m : ℕ}
    (S : Finset (Fin m →₀ ℕ)) (N : ℕ)
    (hbox : ∀ a ∈ S, ∀ i, a i < N) :
    Fintype.card {a // a ∈ S} ≤ N ^ m := by
  sorry
