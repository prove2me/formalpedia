-- Prove2me | Theorems.Thm_MWCSherali_theorem_3_2
-- name    : MWCSherali.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:17.535774+00:00
-- url     : https://prove2.me/theorems/9432d5d5-57a0-4a15-89a5-bff088271b9d
-- title:
--   Theorem 3.2 — Flow LP solutions lift to dual solutions
-- statement:
--   Let $k\ge2$ and $n\ge1$ be integers. For any feasible solution $(f_{a,x,i})$, $(b_{x,i})$ of (Flow-LP) there is a feasible solution $(y_C)_C$, $(z_{C,x,a})_{C,x,a}$, $(w_e)_e$ of (dual-LP$^{\mathrm{no}}_{\mathrm{vertex}}$-w) with
--
--   $$\sum_{C\in D_{k,n}}y_C\ \ge\ \frac{2kn}{kn+\sum_{x\in\Delta_{k,n}}\sum_{i=1}^kb_{x,i}} .$$
--
--   Consequently $2kn/(kn+q_{k,n})$ is a lower bound for the optimum of (dual-LP$^{\mathrm{no}}_{\mathrm{vertex}}$-w), which is much cheaper to compute.
--
--   Differences from the source:
--   - encoding: points x ∈ Δ_{k,n} with coordinates in (1/n)ℤ, 1-based indices → integer coordinates y = n x (Grid k n), 0-based indices; reason: Lean convention; the same points
--   - encoding: labels [k+1] with neutral label k+1 → labels Fin (k+1), terminal i as i − 1, neutral label as Fin.last k; reason: Lean convention; same labelings
--   - encoding: cells C ∈ D_{k,n} → cells indexed by V ∈ Δ_{k,n+1} (Grid k (n+1)); reason: the paper's one-to-one correspondence D_{k,n} ↔ Δ_{k,n+1} (p.15)
--   - encoding: flow variables f_{a,x,i} for a ∈ supp(x), i ≠ a → a total function f with f ≥ 0 everywhere; reason: values outside the variables enter no constraint and can be 0
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 3.2, p.24

import Mathlib
import Definitions.Def_MWCSherali_Grid
import Definitions.Def_MWCSherali_FlowFeasible
import Definitions.Def_MWCSherali_DualVertexWFeasible

namespace MWCSherali

/-- **Theorem 3.2 (Flow LP solutions lift to dual solutions).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Theorem 3.2, p.24:
"Let `k ≥ 2` and `n ≥ 1` be integers. For any feasible solution `(f_{a,x,i}), (b_{x,i})` to
(Flow-LP), there exists a feasible solution `(y_C)_C, (z_{C,x,a})_{C,x,a}, (w_e)_e` to
(dual-LP^no_vertex-w) such that
`∑_{C ∈ D_{k,n}} y_C ≥ 2kn / (kn + ∑_{x ∈ Δ_{k,n}} ∑_{i=1}^k b_{x,i})`."

**Formalization Note.** Cells are indexed by `V : Grid k (n+1)`. The denominator is positive
(`kn ≥ 2`, `b ≥ 0`), so the real division has no junk value. -/
theorem theorem_3_2 (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) (f : Fin k → Grid k n → Fin k → ℝ)
    (b : Grid k n → Fin k → ℝ) (h : FlowFeasible k n f b) :
    ∃ (y : Grid k (n + 1) → ℝ) (z : Grid k (n + 1) → Grid k n → Fin (k + 1) → ℝ)
      (w : Sym2 (Grid k n) → ℝ), DualVertexWFeasible k n y z w ∧
        2 * k * n / (k * n + ∑ x, ∑ i, b x i) ≤ ∑ V, y V := by sorry

end MWCSherali
