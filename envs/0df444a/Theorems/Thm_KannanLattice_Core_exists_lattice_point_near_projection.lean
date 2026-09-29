-- Prove2me | Theorems.Thm_KannanLattice_Core_exists_lattice_point_near_projection
-- name    : KannanLattice.Core.exists_lattice_point_near_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:13:45.419986+00:00
-- url     : https://prove2.me/theorems/d391f863-5dce-485a-a41e-4a6123f5a85f
-- title:
--   Proposition 4.2 — a lattice point within ½(Σ b_j(j)²)^{1/2} of the projection of any point
-- statement:
--   Let $b_1,\dots,b_m$ be linearly independent vectors of $\mathcal R^k$, $L=L(b_1,\dots,b_m)$, and let $b_0\in\mathcal R^k$ be arbitrary. Let $\bar b_0$ be the orthogonal projection of $b_0$ onto $\operatorname{span}\{b_1,\dots,b_m\}$. Then there is a point $b\in L$ with
--
--   $$|b-\bar b_0|\le \frac12\Big(\sum_{j=1}^m b_j(j)^2\Big)^{1/2},$$
--
--   and consequently, for every index $i$ with $b_i(i)=\max_j b_j(j)$,
--
--   $$|\bar b_0-b|\le \frac{\sqrt m}{2}\, b_i(i).$$
--
--   Here $b_j(j)=|b_j^*|$ is the $j$-th Gram–Schmidt length. This is the covering estimate behind nearest-plane rounding; it bounds the distance from any point of the span to the lattice by the Gram–Schmidt lengths of any basis (no reducedness is needed).
--
--   **Formalization Note** The paper's second sentence reads $|b_0-b|\le\frac{\sqrt n}{2}b_i(i)$, with $b_0$ in place of $\bar b_0$. For $k>m$ and $b_0$ off the span that is false, since $|b_0-b|^2=|b_0-\bar b_0|^2+|\bar b_0-b|^2$; the paper uses it only with $k=n$, where $\bar b_0=b_0$. The statement here uses $\bar b_0$, which follows from the first sentence. Both inequalities are asserted for the same lattice point $b$.
-- source:
--   Kannan, Minkowski's Convex Body Theorem and Integer Programming, Math. Oper. Res. 12 (1987); author's final manuscript (CMU-CS-96-105), p. 23, Proposition 4.2 (second sentence with b̄₀ for b₀)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace KannanLattice.Core

/-- Proposition 4.2 of Kannan (1987), p. 23: for a lattice `L(b)` in `ℝᵏ` and any `b₀ ∈ ℝᵏ` with
orthogonal projection `b̄₀` onto `span_ℝ(b)`, some lattice point `v` satisfies
`|v − b̄₀| ≤ ½ (Σ_j b_j(j)²)^{1/2}`, and hence `|b̄₀ − v| ≤ (√m/2) b_i(i)` for every `i` at which
`b_i(i)` is maximal. (The paper's second sentence has `b₀` for `b̄₀`; corrected here.) -/
theorem exists_lattice_point_near_projection (m k : ℕ)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (b₀ : EuclideanSpace ℝ (Fin k)) :
    ∃ v ∈ lattice b,
      ‖v - (Submodule.span ℝ (Set.range b)).starProjection b₀‖ ≤
          (1 / 2 : ℝ) * Real.sqrt (∑ j, gsLen b j ^ 2) ∧
      ∀ i : Fin m, (∀ j : Fin m, gsLen b j ≤ gsLen b i) →
        ‖(Submodule.span ℝ (Set.range b)).starProjection b₀ - v‖ ≤
          Real.sqrt m / 2 * gsLen b i := by sorry

end KannanLattice.Core
