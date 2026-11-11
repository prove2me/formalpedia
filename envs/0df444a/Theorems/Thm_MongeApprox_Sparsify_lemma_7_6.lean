-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_lemma_7_6
-- name    : MongeApprox.Sparsify.lemma_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:02:07.620206+00:00
-- url     : https://prove2.me/theorems/5cbb9bf4-fc9e-42b0-9b43-4d9dff000e3c
-- title:
--   Lemma 7.6 — few points when each has at most t points strictly to its lower left
-- statement:
--   Let $m\ge1$ and $t\ge0$ (real), and let $S\subseteq[0..m)\times[0..m)$ be a set of positions such that for every element $(a,b)$ of $S$, at most $t$ elements of $S$ lie strictly to the lower left of $(a,b)$. Then $|S|\le 2m(\sqrt t+1)$.
--
--   Differences from the source:
--   - encoding: S ⊆ [0..m) × [0..m) → S : Finset (ℤ × ℤ) with both coordinates in [0, m); reason: positions are integer pairs, as in the paper
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), Lemma 7.6, printed p. 37 (PDF 39)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Quadrant

namespace MongeApprox.Sparsify

open Classical in
/-- Lemma 7.6: let `m ≥ 1`, `t ≥ 0` (real), and `S ⊆ [0..m) × [0..m)` a set of positions such that
for every `(a, b) ∈ S` at most `t` elements of `S` lie strictly to the lower left of `(a, b)`.
Then `|S| ≤ 2m(√t + 1)`. -/
theorem lemma_7_6 (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (ht : 0 ≤ t) (S : Finset (ℤ × ℤ))
    (hS : ∀ z ∈ S, 0 ≤ z.1 ∧ z.1 < m ∧ 0 ≤ z.2 ∧ z.2 < m)
    (hlow : ∀ z ∈ S,
      ((S.filter fun w => StrictlyLowerLeft w.1 w.2 z.1 z.2).card : ℝ) ≤ t) :
    (S.card : ℝ) ≤ 2 * m * (Real.sqrt t + 1) := by sorry

end MongeApprox.Sparsify
