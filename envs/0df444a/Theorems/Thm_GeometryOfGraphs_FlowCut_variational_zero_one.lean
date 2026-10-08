-- Prove2me | Theorems.Thm_GeometryOfGraphs_FlowCut_variational_zero_one
-- name    : GeometryOfGraphs.FlowCut.variational_zero_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:08:20.027507+00:00
-- url     : https://prove2.me/theorems/816a2a3d-95ed-491c-ac8f-2bd4c5d74dc2
-- title:
--   §4, proof of Thm 4.1 (pp. 227–228) — min of Σa|zᵢ−zⱼ| / Σb|zᵢ−zⱼ| is attained at a 0/1 vector
-- statement:
--   Let $V$ be a finite set and let $a_{ij} = a_{ji}$ be real weights and $b_{ij} = b_{ji} \ge 0$ be weights on pairs of elements of $V$. For $z \in \mathbb R^V$ consider
--   $$R(z) = \frac{\sum_{i \ne j} a_{ij}\,|z_i - z_j|}{\sum_{i \ne j} b_{ij}\,|z_i - z_j|}.$$
--   The minimum of $R$ over real vectors with a nonzero denominator is attained at a 0/1 vector: for every $z$ with $\sum_{i\ne j} b_{ij}|z_i - z_j| > 0$ there is a set $S \subseteq V$ whose indicator vector $\mathbf 1_S$ also has a positive denominator and satisfies $R(\mathbf 1_S) \le R(z)$.
--
--   With $a = C$ and $b$ the demand weights, $R(\mathbf 1_S) = \mathrm{Cap}(S)/\mathrm{Dem}(S)$, so this is the step of the proof of Theorem 4.1 that turns the best coordinate of an $\ell_1$ embedding into an actual cut.
--
--   **Formalization Note** The page says "for any real $a_{ij} = a_{ji}$, $b_{ij} = b_{ji}$". The statement adds $b \ge 0$, which the page's argument needs (it treats the expression as a ratio of two linear functions whose denominator stays positive) and which holds in the application (capacities and demands). The minimum is taken over $z$ with a nonzero denominator, where the ratio is defined. The inequality is cross-multiplied, and the sums run over all ordered pairs, the diagonal terms being zero.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), pp. 227–228, proof of Theorem 4.1, paragraph 'To justify the assumption'

import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- §4, proof of Theorem 4.1 (pp. 227–228): for symmetric real weights `a` and nonnegative weights `b`, the
minimum over real vectors `z` of `Σ_{i≠j} a_{ij} |z_i - z_j| / Σ_{i≠j} b_{ij} |z_i - z_j|` is attained
at a 0/1 vector. Stated as: every `z` with positive denominator is matched or beaten (cross-multiplied)
by the indicator vector `1_S` of some vertex set `S`, which also has positive denominator. Diagonal
terms vanish, so the sums run over all ordered pairs. The page says "any real a, b";
nonnegativity of `b` is added (see the mission notes). -/
theorem variational_zero_one {V : Type*} [Fintype V] [DecidableEq V] (a b : V → V → ℝ)
    (hb : ∀ i j, 0 ≤ b i j)
    (ha_symm : ∀ i j, a i j = a j i) (hb_symm : ∀ i j, b i j = b j i)
    (z : V → ℝ) (hz : 0 < ∑ i, ∑ j, b i j * |z i - z j|) :
    ∃ S : Finset V,
      0 < ∑ i, ∑ j, b i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)| ∧
      (∑ i, ∑ j, a i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) *
          (∑ i, ∑ j, b i j * |z i - z j|) ≤
        (∑ i, ∑ j, a i j * |z i - z j|) *
          (∑ i, ∑ j, b i j * |(if i ∈ S then (1 : ℝ) else 0) - (if j ∈ S then 1 else 0)|) := by sorry

end GeometryOfGraphs.FlowCut
