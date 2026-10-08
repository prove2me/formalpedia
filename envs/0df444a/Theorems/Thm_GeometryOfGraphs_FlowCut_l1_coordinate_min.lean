-- Prove2me | Theorems.Thm_GeometryOfGraphs_FlowCut_l1_coordinate_min
-- name    : GeometryOfGraphs.FlowCut.l1_coordinate_min
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:43:11.087074+00:00
-- url     : https://prove2.me/theorems/2a10f266-d31c-4bdd-9449-3d7c7238d151
-- title:
--   §4, proof of Thm 4.1, second and third displays (p. 227) — the ℓ₁ ratio is at least its best single coordinate
-- statement:
--   Let $N$ be a multicommodity flow network on a finite vertex set $V$ with capacities $C$ and commodities $(s_\mu, t_\mu, D_\mu)_{\mu=1}^k$, and let $x_i \in \mathbb R^m$ for $i \in V$, with coordinates $x_{i,r}$. Suppose $\sum_\mu D_\mu \|x_{s_\mu} - x_{t_\mu}\|_1 > 0$. Then there is a coordinate $r$ with $\sum_\mu D_\mu |x_{s_\mu,r} - x_{t_\mu,r}| > 0$ and
--   $$\frac{\sum_{\{i,j\}} C_{i,j}\,|x_{i,r} - x_{j,r}|}{\sum_{\mu} D_\mu\,|x_{s_\mu,r} - x_{t_\mu,r}|} \le \frac{\sum_{\{i,j\}} C_{i,j}\,\|x_i - x_j\|_1}{\sum_{\mu} D_\mu\,\|x_{s_\mu} - x_{t_\mu}\|_1},$$
--   the numerators summing over unordered pairs $\{i,j\}$.
--
--   Because the $\ell_1$ norm is a sum over coordinates, both sides of the full ratio split as sums over $r$, and a ratio of sums is at least the smallest of the coordinate ratios. In the proof of Theorem 4.1 this reduces an $\ell_1^m$ embedding to a single line.
--
--   **Formalization Note** The inequality is stated cross-multiplied. As in the LP-duality display, the page's $\sum_{i \ne j}$ over ordered pairs is replaced by the unordered-pair sum $\tfrac12\sum_i\sum_j$; the ratio itself does not change.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 227, proof of Theorem 4.1, second and third displays

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- §4, proof of Theorem 4.1, second and third displays (p. 227): for points `x i ∈ ℝ^m` under the
`ℓ₁` norm, the ratio `Σ_{edges} C_{ij} ‖x_i - x_j‖₁ / Σ_μ D_μ ‖x_{s_μ} - x_{t_μ}‖₁` is at least the
minimum over coordinates `r` of the same ratio for coordinate `r` alone. Stated cross-multiplied:
some coordinate `r` has positive denominator and a ratio no larger than the full one. Edge sums are
over unordered pairs, `(1/2) * Σ_i Σ_j`. -/
theorem l1_coordinate_min {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) {m : ℕ}
    (x : V → Fin m → ℝ)
    (hpos : 0 < ∑ μ, N.D μ * ∑ r, |x (N.s μ) r - x (N.t μ) r|) :
    ∃ r : Fin m, 0 < ∑ μ, N.D μ * |x (N.s μ) r - x (N.t μ) r| ∧
      ((1 / 2) * ∑ i, ∑ j, N.C i j * |x i r - x j r|) *
          (∑ μ, N.D μ * ∑ r', |x (N.s μ) r' - x (N.t μ) r'|) ≤
        ((1 / 2) * ∑ i, ∑ j, N.C i j * ∑ r', |x i r' - x j r'|) *
          (∑ μ, N.D μ * |x (N.s μ) r - x (N.t μ) r|) := by sorry

end GeometryOfGraphs.FlowCut
