-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_slope_lowerSemicontinuous
-- name    : NonsmoothLojasiewicz.Continuous.slope_lowerSemicontinuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:14:09.062987+00:00
-- url     : https://prove2.me/theorems/3d39cc37-f799-4289-87a7-5d6fae22e5a8
-- title:
--   Remark 2.12 (closed-domain continuous case): the slope $m_f$ is lower semicontinuous
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ have closed domain and be continuous relative to its domain, and let $m_f(x) = \inf\{\|x^*\| : x^* \in \partial f(x)\} \in [0, +\infty]$ be its nonsmooth slope. Then $m_f$ is lower semicontinuous on $\mathbb{R}^n$:
--   $$
--   m_f(x) \le \liminf_{y \to x} m_f(y) \qquad \text{for every } x \in \mathbb{R}^n.
--   $$
--
--   The proof of Theorem 3.1 uses this to realise the infimum of $m_f$ over a compact piece of a level set.
--
--   **Formalization Note.** The slope takes values in `ℝ≥0∞`, with $m_f(x) = +\infty$ where $\partial f(x) = \emptyset$; lower semicontinuity is Mathlib's `LowerSemicontinuous` for this order. Only the closed-domain continuous case of Remark 2.12 is formalized.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211 (PDF p. 7), Remark 2.12, clause on the slope m_f (case dom f closed and f|dom f continuous)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Remark 2.12 (p. 1211), case "dom f closed and f|dom f continuous":
the slope `m_f` of (4) is lower semicontinuous (values in `[0, +∞]`). -/
theorem slope_lowerSemicontinuous {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) :
    LowerSemicontinuous (slope f) := by sorry

end NonsmoothLojasiewicz.Continuous
