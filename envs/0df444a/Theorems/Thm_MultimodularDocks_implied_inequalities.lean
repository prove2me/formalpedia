-- Prove2me | Theorems.Thm_MultimodularDocks_implied_inequalities
-- name    : MultimodularDocks.implied_inequalities
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:35:31.013273+00:00
-- url     : https://prove2.me/theorems/596eb7d7-8d4f-4b9d-9f77-7403fcb4321a
-- title:
--   Definition 1, (4)–(6) (corrected: Definition 1 on the quadrant) — implied inequalities of a multimodular function
-- statement:
--   Consider, for $f:\mathbb Z\times\mathbb Z\to\mathbb R$ and $d,b\ge 0$, the inequalities
--
--   $$
--   \begin{aligned}
--   f(d+2,b)-f(d+1,b)&\ge f(d+1,b)-f(d,b), &&(4)\\
--   f(d,b+2)-f(d,b+1)&\ge f(d,b+1)-f(d,b), &&(5)\\
--   f(d+1,b+1)-f(d,b+1)&\ge f(d+1,b)-f(d,b). &&(6)
--   \end{aligned}
--   $$
--
--   With inequalities (1)–(3) of Definition 1 required wherever all their arguments are nonnegative: (6) and (1) are equivalent at every $d,b\ge 0$; if (1) and (2) hold, then (5) holds for all $d,b\ge 0$; if (3) and (6) hold, then (4) holds for all $d,b\ge 0$. In particular every multimodular $f$ satisfies (4), (5) and (6) for all $d,b\ge 0$.
--
--   Inequalities (4) and (5) say that $f$ is convex in empty docks and in full docks separately; (6) is (1) rearranged. They are used repeatedly in the proofs of Lemmas 3.3 and 3.4.
--
--   Differences from the source:
--   - correction: Definition 1 (p.10): (1)–(3) for all d, b ∈ ℤ for f : ℤ² → ℝ ∪ {∞} with ∞ − ∞ = ∞, station costs c_i = ∞ off their band (p.11) → IsMultimodular: a real f : ℤ → ℤ → ℝ satisfies (1)–(3) whenever all arguments are ≥ 0; the band is carried separately (InBand, Feasible); reason: with the printed convention Lemma 2.1 is false (X empty, l = 0, u = 2, so c_i = 0 on its band: (1) at d = −1, b = 0 reads 0 ≥ ∞ − ∞ = ∞); the other reading, (1)–(3) whenever all four terms are finite, makes Theorem 1 false (two stations, l = u = 2, B = D = 2, g_A(2 − k, k) = 1, 3, 0 for k = 0, 1, 2, g_B = 0: from b = (0, 2) Algorithm 1 stops at cost 1 while (2, 0) costs 0 at dock-move distance 0)
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, Definition 1, p.10, inequalities (4)–(6)

import Mathlib
import Definitions.Def_MultimodularDocks_IsMultimodular

namespace MultimodularDocks

/-- **The implied inequalities (4)–(6)** (Freund, Henderson, Shmoys, arXiv:1611.09304v5,
Definition 1, p.10: "(6) & (1) are equivalent, (1) & (2) imply (5), and (3) & (6) imply (4)").
For any `f : ℤ → ℤ → ℝ`, with every inequality required where all its arguments are
nonnegative (as in `IsMultimodular`):
* (6) `f (d+1) (b+1) − f d (b+1) ≥ f (d+1) b − f d b` and (1) are equivalent at every
  `d, b ≥ 0`;
* if (1) and (2) hold, then (5) `f d (b+2) − f d (b+1) ≥ f d (b+1) − f d b` for all
  `d, b ≥ 0`;
* if (3) and (6) hold, then (4) `f (d+2) b − f (d+1) b ≥ f (d+1) b − f d b` for all
  `d, b ≥ 0`;
* in particular a multimodular `f` satisfies (4), (5) and (6) at all `d, b ≥ 0`.

**Formalization Note** (1)–(3) are on the quadrant, as in `IsMultimodular` (Definition 1
corrected); (6), (5), (4) are claimed for all `d, b ≥ 0`, where all their arguments are
nonnegative. -/
theorem implied_inequalities (f : ℤ → ℤ → ℝ) :
    (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      (f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1) ↔
        f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b)) ∧
    ((∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f d (b + 1) - f d b ≤ f (d + 1) (b + 1) - f (d + 1) b) →
      (∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
        f d b - f d (b - 1) ≤ f (d - 1) (b + 1) - f (d - 1) b) →
      ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f d (b + 1) - f d b ≤ f d (b + 2) - f d (b + 1)) ∧
    ((∀ d b : ℤ, 1 ≤ d → 1 ≤ b →
        f d b - f (d - 1) b ≤ f (d + 1) (b - 1) - f d (b - 1)) →
      (∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1)) →
      ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
        f (d + 1) b - f d b ≤ f (d + 2) b - f (d + 1) b) ∧
    (IsMultimodular f → ∀ d b : ℤ, 0 ≤ d → 0 ≤ b →
      f (d + 1) b - f d b ≤ f (d + 2) b - f (d + 1) b ∧
        f d (b + 1) - f d b ≤ f d (b + 2) - f d (b + 1) ∧
        f (d + 1) b - f d b ≤ f (d + 1) (b + 1) - f d (b + 1)) := by sorry

end MultimodularDocks
