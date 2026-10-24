-- Prove2me | Theorems.Thm_ModernConvex_SLemma_zero_set_projective_connected
-- name    : ModernConvex.SLemma.zero_set_projective_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:47.075984+00:00
-- url     : https://prove2.me/theorems/57f1c7b4-9682-49be-94de-33454efce1a0
-- title:
--   Proposition 4.10.4 — the zero set of a quadratic form on Sⁿ⁻¹ (n ≥ 3) has a connected projective image
-- statement:
--   Let $f(x) = x^TQx$ be a homogeneous quadratic form on $\mathbb R^n$ with $n \ge 3$, and assume that the set
--   $$Y = \{x \in S^{n-1} : f(x) = 0\}$$
--   is nonempty. Then $Y$ is centrally symmetric ($Y = -Y$), and its image $Z = \Phi(Y)$ under the canonical projection $\Phi : S^{n-1} \to P^{n-1}$ is connected.
--
--   This is the key step in the proof of Polyak's theorem (SL.D). The restriction $n \ge 3$ is essential: for $n = 2$ and $f(x) = x_1x_2$, $Z$ consists of two distinct points of $P^1$.
--
--   **Formalization Note** The sphere is `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1`. A point `x` of it is turned into a vector `Fin n → ℝ` by `WithLp.ofLp`, so that $f(x)$ is `x ⬝ᵥ (Q *ᵥ x)`. $Q$ is any real $n\times n$ matrix. The page does not say symmetric, and $x^TQx$ depends only on the symmetric part of $Q$. $P^{n-1}$ is `ProjSpace n` with the quotient topology, from `ModernConvex.SLemma.ProjectiveSpace`. "Connected" is Mathlib's `IsConnected`, which includes nonemptiness; that follows from the hypothesis $Y \ne \emptyset$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 308, Proposition 4.10.4 (Exercise 4.52)

import Mathlib
import Definitions.Def_ModernConvex_SLemma_ProjectiveSpace

open Matrix

namespace ModernConvex.SLemma

/-- Ben-Tal–Nemirovski, Proposition 4.10.4, p. 308: let `f(x) = xᵀQx` be a homogeneous quadratic
form on `ℝⁿ`, `n ≥ 3`, and assume that `Y = {x ∈ Sⁿ⁻¹ : f(x) = 0}` is nonempty. Then `Y` is
centrally symmetric and its image `Z = Φ(Y)` under the canonical projection
`Φ : Sⁿ⁻¹ → Pⁿ⁻¹` is connected. -/
theorem zero_set_projective_connected {n : ℕ} (hn : 3 ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hY : {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0}.Nonempty) :
    (∀ x ∈ {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
          (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0},
      -x ∈ {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
          (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0}) ∧
    IsConnected (canonicalProjection n '' {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
      WithLp.ofLp (x : EuclideanSpace ℝ (Fin n)) ⬝ᵥ
        (Q *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ (Fin n))) = 0}) := by sorry

end ModernConvex.SLemma
