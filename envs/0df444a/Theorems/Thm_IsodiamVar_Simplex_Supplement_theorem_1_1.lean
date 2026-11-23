-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_Supplement_theorem_1_1
-- name    : IsodiamVar.Simplex.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:51:26.551174+00:00
-- url     : https://prove2.me/theorems/ac769600-dea1-4e9d-818e-54638647f80d
-- title:
--   Theorem 1.1 — enclosing spheres support variance maximizers, parts (a) and (b)
-- statement:
--   Let $K\subseteq\mathbb R^n$ be compact and let $\mu\in\mathcal P(K)$. Write $m=\bar x(\mu)$, and let $\phi_K^{**}$ be the biconjugate of the function $-|x|^2$ on $K$, extended by $+\infty$ elsewhere.
--
--   (a) The variance satisfies
--
--   $$\operatorname{Var}(\mu)\le-|m|^2-\phi_K^{**}(m).$$
--
--   If $m$ lies in the ambient interior of the closed convex hull of $K$, equality holds if and only if there exist $q\in\mathbb R^n$ and $R\ge0$ such that
--
--   $$K\subseteq\overline B_R(q),\qquad
--   \mu\bigl(K\cap\{x:|x-q|=R\}\bigr)=1.$$
--
--   The interior hypothesis applies only to this equality characterization. The enclosing ball here need not be a globally smallest one.
--
--   (b) The measure $\mu$ maximizes variance over all $\mathcal P(K)$, allowing every barycenter, if and only if there is a globally smallest enclosing closed ball $\overline B_R(q)$ such that
--
--   $$\mu\bigl(K\cap\{x:|x-q|=R\}\bigr)=1,\qquad \bar x(\mu)=q.$$
--
--   For any smallest enclosing ball, a maximizing measure has
--
--   $$\operatorname{Var}(\mu)=R^2.$$
--
--   This is the complete multidimensional variance bound and optimizer characterization. Compact sets may be infinite, nonconvex or lower-dimensional. The existence of $\mu\in\mathcal P(K)$ already implies $K$ is nonempty; no such extra premise is added. A sphere is its distance level set, so radius zero includes the singleton equality case.
--
--   Differences from the source:
--   - encoding: Euclidean probabilities, integrals, convex envelopes and geometric enclosing spheres → The published Euclidean space and InP predicate, EReal conjugates, and closed balls with nonnegative radii and distance-level spheres; reason: These retain arbitrary compact sets, genuine empty extrema, and radius-zero contact without adding a hypothesis.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 3, Theorem 1.1

import Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre
import Definitions.Def_IsodiamVar_Simplex_Supplement_Variance

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Theorem 1.1(a),(b), p. 3. No interior assumption on the bound or global optimization.
Sphere means the distance level set, also at radius zero. -/
theorem theorem_1_1 {n : ℕ} (K : Set (E n)) (hK : IsCompact K)
    (μ : Measure (E n)) (hμ : InP K μ) :
    ((variance μ : EReal) ≤
      ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - phiBiconjugate K (barycenter μ)) ∧
    (barycenter μ ∈ interior (closedConvexHull ℝ K) →
      (((variance μ : EReal) =
          ((-(‖barycenter μ‖ ^ 2) : ℝ) : EReal) - phiBiconjugate K (barycenter μ)) ↔
        ∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
          μ (K ∩ Metric.sphere q R) = 1)) ∧
    (((∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) ↔
      ∃ q : E n, ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
        (∀ c : E n, ∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall c r → R ≤ r) ∧
        μ (K ∩ Metric.sphere q R) = 1 ∧ barycenter μ = q)) ∧
    (∀ q : E n, ∀ R : ℝ, 0 ≤ R → K ⊆ Metric.closedBall q R →
      (∀ c : E n, ∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall c r → R ≤ r) →
      (∀ ν : Measure (E n), InP K ν → variance ν ≤ variance μ) → variance μ = R ^ 2) := by sorry

end IsodiamVar.Simplex.Supplement
