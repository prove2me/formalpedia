-- Prove2me | Theorems.Thm_MultimodularDocks_marginal_bike
-- name    : MultimodularDocks.marginal_bike
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:31.309975+00:00
-- url     : https://prove2.me/theorems/146551cf-d220-416b-9f00-def27cc02f1c
-- title:
--   Lemma 3.3, Cases 3.b)–4.b) (corrected: Definition 1 on the quadrant) — station inequality for a moved bike
-- statement:
--   Let $f$ be multimodular and $d,b,d',b'\ge 0$.
--
--   1. If $d'+b'\le d+b$ and $b<b'$, then $f(d,b)-f(d-1,b+1)\ge f(d'+1,b'-1)-f(d',b')$.
--   2. If $d+b\le d'+b'$ and $b'<b$, then $f(d,b)-f(d+1,b-1)\ge f(d'-1,b'+1)-f(d',b')$.
--
--   In words: a station with too few bikes relative to a better allocation, and at least as many docks, gains at least as much from one more bike as the better allocation loses by giving one up.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
--   - generalization: the inequality for station ℓ's UDF in Case 3.b), with Case 4.b) 'symmetric' → two inequalities for any multimodular f and any nonnegative (d, b), (d', b') with the stated order relations; reason: the page's derivation uses only Fact 1 and (3); the UDF is multimodular by Lemma 2.1; clause 2 writes out the symmetric case
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, proof of Lemma 3.3, App. C.2.1, Case 3.b), p.48; Case 4.b) symmetric, p.46

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

namespace MultimodularDocks

/-- **Station inequality for a moved bike** (Freund, Henderson, Shmoys, arXiv:1611.09304v5,
proof of Lemma 3.3, Case 3.b), p.48, and the symmetric Case 4.b)). Let `f` be multimodular and
`d, b, d', b' ≥ 0`.
1. If `d' + b' ≤ d + b` and `b < b'`:
   `f(d, b) − f(d − 1, b + 1) ≥ f(d' + 1, b' − 1) − f(d', b')`.
2. If `d + b ≤ d' + b'` and `b' < b`:
   `f(d, b) − f(d + 1, b − 1) ≥ f(d' − 1, b' + 1) − f(d', b')`.

**Formalization Note** Clause 2 is the mirror case the page calls symmetric, written out. -/
theorem marginal_bike (f : ℤ → ℤ → ℝ) (hf : IsMultimodular f) (d b d' b' : ℤ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (hd' : 0 ≤ d') (hb' : 0 ≤ b') :
    (d' + b' ≤ d + b → b < b' → f (d' + 1) (b' - 1) - f d' b' ≤ f d b - f (d - 1) (b + 1)) ∧
      (d + b ≤ d' + b' → b' < b →
        f (d' - 1) (b' + 1) - f d' b' ≤ f d b - f (d + 1) (b - 1)) := by sorry

end MultimodularDocks
