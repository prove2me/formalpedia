-- Prove2me | Theorems.Thm_IsodiamVar_Simplex_Supplement_proposition_2_1
-- name    : IsodiamVar.Simplex.Supplement.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:49:53.415483+00:00
-- url     : https://prove2.me/theorems/91904b0e-c6ab-46c5-9644-99df0c9f18e9
-- title:
--   Proposition 2.1 — strong duality, attainment, and optimal-pair contact sets
-- statement:
--   Let $K\subseteq\mathbb R^n$ be compact, $L$ its closed convex hull, and $\mathcal P_0(K)$ the Borel probabilities carried by $K$ with zero barycenter. With $\phi_K$ and its conjugates defined by (1.5)–(1.6), put
--
--   $$P=\sup_{\mu\in\mathcal P_0(K)}\int |x|^2\,d\mu(x),\qquad
--   D=\inf_{q\in\mathbb R^n}\phi_K^*(-2q).$$
--
--   Then
--
--   $$P=D=-\phi_K^{**}(0).$$
--
--   The supremum is attained if $0\in L$, and the infimum is attained if $0\in\operatorname{int}L$. These are separate conditional conclusions, not premises for the value identity. For every $\mu\in\mathcal P_0(K)$ and $q\in\mathbb R^n$, the pair optimizes the primal and dual problems if and only if, for the least nonnegative radius $R$ enclosing $K$ with this fixed center $q$,
--
--   $$\mu\bigl(K\cap\{x:|x-q|=R\}\bigr)=1.$$
--
--   This gives the duality and equality characterization used by Theorem 1.1. Extrema are extended-real: if the primal class is empty, $P=-\infty$. No nonempty, full-dimensional or convex-set hypothesis is imposed on $K$.
--
--   Differences from the source:
--   - encoding: Euclidean probabilities, integrals, convex envelopes and geometric enclosing spheres → The published Euclidean space and InP predicate, EReal conjugates, and closed balls with nonnegative radii and distance-level spheres; reason: These retain arbitrary compact sets, genuine empty extrema, and radius-zero contact without adding a hypothesis.
-- source:
--   Lim & McCann, Geometrical bounds for the variance and recentered moments, arXiv:2001.11851v1, p. 8, Proposition 2.1

import Definitions.Def_IsodiamVar_Simplex_Supplement_Legendre
import Definitions.Def_IsodiamVar_Simplex_Supplement_ZeroMean

open MeasureTheory

namespace IsodiamVar.Simplex.Supplement

/-- Proposition 2.1, p. 8; proof pp. 9–11. Empty and infeasible cases use EReal. -/
theorem proposition_2_1 {n : ℕ} (K : Set (E n)) (hK : IsCompact K) :
    let primal : EReal := ⨆ μ : {μ : Measure (E n) // InP0 K μ},
      ((∫ x, ‖x‖ ^ 2 ∂μ.val : ℝ) : EReal)
    let dual : EReal := ⨅ q : E n, phiStar K ((-2 : ℝ) • q)
    primal = dual ∧ dual = -phiBiconjugate K 0 ∧
    (0 ∈ closedConvexHull ℝ K →
      ∃ μ : Measure (E n), InP0 K μ ∧ ((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) = primal) ∧
    (0 ∈ interior (closedConvexHull ℝ K) →
      ∃ q : E n, phiStar K ((-2 : ℝ) • q) = dual) ∧
    (∀ μ : Measure (E n), InP0 K μ → ∀ q : E n,
      ((((∫ x, ‖x‖ ^ 2 ∂μ : ℝ) : EReal) = primal ∧
          phiStar K ((-2 : ℝ) • q) = dual) ↔
        ∃ R : ℝ, 0 ≤ R ∧ K ⊆ Metric.closedBall q R ∧
          (∀ r : ℝ, 0 ≤ r → K ⊆ Metric.closedBall q r → R ≤ r) ∧
          μ (K ∩ Metric.sphere q R) = 1)) := by sorry

end IsodiamVar.Simplex.Supplement
