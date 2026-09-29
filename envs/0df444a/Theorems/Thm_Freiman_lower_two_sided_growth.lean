-- Prove2me | Theorems.Thm_Freiman_lower_two_sided_growth
-- name    : Freiman.lower_two_sided_growth
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:56.417903+00:00
-- url     : https://prove2.me/theorems/f9281e17-b8e7-41f3-9ea2-566c352de478
-- title:
--   Freiman lower construction: two sided growth
-- statement:
--   A positive eventually fixed width contradicts extension of the wider side within two steps, while the other prefix grows and its width tends to zero. This is the abstract real/natural-number limiting argument.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, proof of lem:lc-both-shrink

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_two_sided_growth (hw : ∀ w : List ℕ+, 0 < lowerWidth w ∧ lowerWidth w ≤ 1 / ((Nat.fib (w.length+1) : ℝ)^2))
    (hm : ∀ w u : List ℕ+, (∀ d ∈ u, (d : ℕ) ≤ 3) → lowerWidth (w++u) ≤ lowerWidth w)
    (h : ℕ → LowerPair) (he : ∀ n, lowerExtends (h n) (h (n+1)))
    (hp : ∀ n, lowerPrefixSize (h n) < lowerPrefixSize (h (n+1))) (hf : lowerWithinTwo h) :
    Filter.Tendsto (fun n => (h n).1.length) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun n => (h n).2.length) Filter.atTop Filter.atTop := by
  sorry
