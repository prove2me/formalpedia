-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_crit_isClosed
-- name    : NonsmoothLojasiewicz.Continuous.crit_isClosed
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:14:06.910983+00:00
-- url     : https://prove2.me/theorems/e2ae0d71-bcf5-4c78-977f-80c0c9769905
-- title:
--   Remark 2.12 (closed-domain continuous case): $\mathrm{crit}\, f$ is closed
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ have closed domain and be continuous relative to its domain. Then the set of critical points
--   $$
--   \operatorname{crit} f = \{x \in \mathbb{R}^n : 0 \in \partial f(x)\}
--   $$
--   is closed, where $\partial f$ is the limiting subdifferential.
--
--   Together with subanalyticity of $\operatorname{crit} f$, this gives the critical set a locally finite number of connected components, the setting in which the constancy of $f$ on each component and Theorem 3.1 are formulated.
--
--   **Formalization Note.** Same encoding as the closed-graph item: `f : EuclideanSpace ℝ (Fin n) → EReal`, never `⊥`, closed domain `{x | f x ≠ ⊤}` and `ContinuousOn f` on it. Only the closed-domain continuous case of Remark 2.12 is formalized.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211 (PDF p. 7), Remark 2.12, clause on crit f (case dom f closed and f|dom f continuous)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Remark 2.12 (p. 1211), case "dom f closed and f|dom f continuous":
the set `crit f` of critical points is closed. -/
theorem crit_isClosed {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) :
    IsClosed (crit f) := by sorry

end NonsmoothLojasiewicz.Continuous
