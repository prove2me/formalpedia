-- Prove2me | Theorems.Thm_GeometryOfGraphs_FlowCut_lp_duality
-- name    : GeometryOfGraphs.FlowCut.lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:58:11.22191+00:00
-- url     : https://prove2.me/theorems/2ca7fa47-9b35-4a12-878e-fd21af1a4e7d
-- title:
--   §4, proof of Thm 4.1, first display (p. 227) — maxflow = min over metrics d of ΣC·d / ΣD·d
-- statement:
--   Let $N$ be a multicommodity flow network on a finite vertex set $V$ with capacities $C$ and commodities $(s_\mu, t_\mu, D_\mu)_{\mu=1}^k$, and suppose some commodity has $D_\mu > 0$ and $s_\mu \ne t_\mu$. Then the maxflow is the minimum, over semi-metrics $d$ on $V$, of the ratio
--   $$\lambda = \min_d \frac{\sum_{\{i,j\}} C_{i,j}\, d_{i,j}}{\sum_{\mu=1}^k D_\mu\, d_{s_\mu,t_\mu}},$$
--   where the numerator sums over unordered pairs $\{i,j\}$. Precisely:
--
--   1. for every semi-metric $d$ on $V$, $\mathrm{maxflow}\cdot\sum_\mu D_\mu d_{s_\mu,t_\mu} \le \sum_{\{i,j\}} C_{i,j} d_{i,j}$;
--   2. some semi-metric $d$ with $\sum_\mu D_\mu d_{s_\mu,t_\mu} > 0$ attains equality.
--
--   The paper obtains this from linear programming duality (citing [24]): the maxflow is the optimum of a linear program whose dual is the metric relaxation of the sparsest cut. It turns the flow problem into a question about a metric, which is where the embedding results of Section 3 enter.
--
--   **Formalization Note** The page writes the numerator as $\sum_{i \ne j} C_{i,j} d_{i,j}$ over ordered pairs, which counts each edge twice while maxflow and $\mathrm{Cap}$ count each edge once; read literally it is off by a factor $2$. The statement uses unordered pairs, written $\tfrac12\sum_i\sum_j C_{i,j} d_{i,j}$. The same convention is used in the coordinate-minimum display, so the chain of the proof is unchanged. "Metric" means semi-metric (p. 218, footnote 1).
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 227, proof of Theorem 4.1, first display

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- §4, proof of Theorem 4.1, first display (p. 227): by LP duality,
`maxflow = min_d (Σ_{edges} C_{ij} d_{ij}) / (Σ_μ D_μ d_{s_μ t_μ})` over (semi-)metrics `d` on `V`.
Stated cross-multiplied: (1) every pseudometric `d` gives an upper bound on `maxflow`; (2) some
pseudometric with positive denominator attains it. Edge sums are over unordered pairs, written as
`(1/2) * Σ_i Σ_j`, so that each edge's capacity is counted once, as in `Cap`. -/
theorem lp_duality {V : Type*} [Fintype V] [DecidableEq V] (N : Network V)
    (hN : ∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) :
    (∀ d : V → V → ℝ, IsPseudometric d →
      N.maxflow * ∑ μ, N.D μ * d (N.s μ) (N.t μ) ≤ (1 / 2) * ∑ i, ∑ j, N.C i j * d i j) ∧
    ∃ d : V → V → ℝ, IsPseudometric d ∧ 0 < ∑ μ, N.D μ * d (N.s μ) (N.t μ) ∧
      N.maxflow * ∑ μ, N.D μ * d (N.s μ) (N.t μ) = (1 / 2) * ∑ i, ∑ j, N.C i j * d i j := by sorry

end GeometryOfGraphs.FlowCut
