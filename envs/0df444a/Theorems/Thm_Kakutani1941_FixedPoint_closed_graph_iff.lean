-- Prove2me | Theorems.Thm_Kakutani1941_FixedPoint_closed_graph_iff
-- name    : Kakutani1941.FixedPoint.closed_graph_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:15:45.865314+00:00
-- url     : https://prove2.me/theorems/3b9c9556-7aaa-4e08-bab9-548380e6b0ce
-- title:
--   Section 1 — upper semi-continuity is equivalent to a closed graph
-- statement:
--   Let $S$ be a closed subset of $\mathbb R^m$ and let $\Phi$ assign to every $x\in S$ a subset $\Phi(x)\subseteq S$. Then $\Phi$ is upper semi-continuous on $S$ in Kakutani's sequential sense (whenever $x_n\in S$, $x_n\to x_0\in S$, $y_n\in\Phi(x_n)$ and $y_n\to y_0$, one has $y_0\in\Phi(x_0)$) if and only if its graph
--
--   $$\operatorname{Graph}\Phi=\bigcup_{x\in S}\{x\}\times\Phi(x)=\{(x,y): x\in S,\ y\in\Phi(x)\}$$
--
--   is a closed subset of $\mathbb R^m\times\mathbb R^m$.
--
--   The equivalence lets one check upper semi-continuity by exhibiting the graph as a closed set; Kakutani's proof of Theorem 2 uses it in this way, for a mapping built from two closed sets.
--
--   **Formalization Note** The page says the graph is "a closed subset of $S\times S$". Since $S$ is closed, $S\times S$ is closed in $\mathbb R^m\times\mathbb R^m$, so closedness relative to $S\times S$ and closedness in the whole product coincide; the Lean states the latter. The page makes this remark for a closed simplex $S$; it is stated here for every closed $S$, which contains that case. The hypothesis $\Phi(x)\subseteq S$ is the page's "mapping of $S$ into $\mathfrak R(S)$" and places the graph inside $S\times S$; closedness and convexity of the values are not assumed.
-- source:
--   Kakutani, A generalization of Brouwer's fixed point theorem, Duke Math. J. 8 (1941), p. 457, Section 1, https://doi.org/10.1215/s0012-7094-41-00838-4

import Mathlib
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous

namespace Kakutani1941.FixedPoint

/-- Section 1, p. 457: for a closed domain, sequential upper semi-continuity is the same as a
closed graph `⋃_{x ∈ S} {x} × Φ(x)`. -/
theorem closed_graph_iff {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSclosed : IsClosed S)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦsub : ∀ x ∈ S, Φ x ⊆ S) :
    IsUpperSemicontinuous S Φ ↔
      IsClosed {p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) |
        p.1 ∈ S ∧ p.2 ∈ Φ p.1} := by sorry

end Kakutani1941.FixedPoint
