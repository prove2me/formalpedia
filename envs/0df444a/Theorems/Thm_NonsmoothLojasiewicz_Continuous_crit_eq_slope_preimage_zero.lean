-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_crit_eq_slope_preimage_zero
-- name    : NonsmoothLojasiewicz.Continuous.crit_eq_slope_preimage_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:14:46.251361+00:00
-- url     : https://prove2.me/theorems/ba086110-8df5-48da-84a2-070b49e0add6
-- title:
--   Remark 2.12 (closed-domain continuous case): $\mathrm{crit}\, f = m_f^{-1}(0)$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ have closed domain and be continuous relative to its domain. Then the critical points of $f$ are exactly the zeros of its nonsmooth slope:
--   $$
--   \operatorname{crit} f = m_f^{-1}(0) = \{x \in \mathbb{R}^n : m_f(x) = 0\}.
--   $$
--
--   One inclusion is immediate; the other says that a slope equal to zero is attained by a zero subgradient, which uses closedness of $\partial f(x)$. The proof of Theorem 3.1 uses this to pass from $m_f(y) = 0$ to $y \in \operatorname{crit} f$.
--
--   **Formalization Note.** The slope is valued in `ℝ≥0∞`, so $m_f^{-1}(0)$ never contains points with $\partial f(x) = \emptyset$ (where $m_f = +\infty$). Only the closed-domain continuous case of Remark 2.12 is formalized.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211 (PDF p. 7), Remark 2.12, clause crit f = m_f^{-1}(0) (case dom f closed and f|dom f continuous)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Remark 2.12 (p. 1211), case "dom f closed and f|dom f continuous":
`crit f = m_f⁻¹(0)`. -/
theorem crit_eq_slope_preimage_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) :
    crit f = slope f ⁻¹' {0} := by sorry

end NonsmoothLojasiewicz.Continuous
