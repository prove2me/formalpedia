-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_limitingSubdiff_graph_isClosed
-- name    : NonsmoothLojasiewicz.Continuous.limitingSubdiff_graph_isClosed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:51:06.54563+00:00
-- url     : https://prove2.me/theorems/58f7216b-350e-4691-98b9-996e703317b8
-- title:
--   Remark 2.12 (closed-domain continuous case): the graph of $\partial f$ is closed
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ have closed domain $\operatorname{dom} f = \{x : f(x) < +\infty\}$ and suppose that the restriction $f|_{\operatorname{dom} f}$ is continuous. Then the graph of the limiting subdifferential,
--   $$
--   \operatorname{Gr} \partial f = \{(x, x^*) \in \mathbb{R}^n \times \mathbb{R}^n : x^* \in \partial f(x)\},
--   $$
--   is a closed subset of $\mathbb{R}^n \times \mathbb{R}^n$.
--
--   Closedness of the graph is what makes the critical set closed and the slope lower semicontinuous in this setting; for general lower semicontinuous functions it can fail because $f(x_k)$ need not converge to $f(x)$.
--
--   **Formalization Note.** `f : EuclideanSpace ℝ (Fin n) → EReal` with `f x ≠ ⊥` for all `x`; the domain is `{x | f x ≠ ⊤}`, assumed closed, and `ContinuousOn f {x | f x ≠ ⊤}` is continuity of the restriction (as a map into the extended reals, which on finite values is ordinary continuity). This item formalizes only the closed-domain continuous case of the remark, not the lower semicontinuous convex case.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211 (PDF p. 7), Remark 2.12, first clause (case dom f closed and f|dom f continuous)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Remark 2.12 (p. 1211), first clause in the case "dom f closed and f|dom f continuous":
the graph of the limiting subdifferential `∂f` is closed in `ℝⁿ × ℝⁿ`. -/
theorem limitingSubdiff_graph_isClosed {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) :
    IsClosed {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      p.2 ∈ NonconvexSplitting.Shared.LimitingSubdiff f p.1} := by sorry

end NonsmoothLojasiewicz.Continuous
