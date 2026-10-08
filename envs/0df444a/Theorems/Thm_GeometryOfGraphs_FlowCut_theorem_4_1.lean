-- Prove2me | Theorems.Thm_GeometryOfGraphs_FlowCut_theorem_4_1
-- name    : GeometryOfGraphs.FlowCut.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:58:04.381584+00:00
-- url     : https://prove2.me/theorems/5c94f44b-72cb-4bee-b359-0348e6cf7d11
-- title:
--   Theorem 4.1 (p. 226) — every multicommodity network has a cut with Cap(S)/Dem(S) ≤ O(log k) · maxflow
-- statement:
--   There is an absolute constant $C_0 > 0$ with the following property. Let $N$ be a multicommodity flow network: a finite vertex set $V$, symmetric capacities $C_{i,j} \ge 0$ (zero on non-edges and on the diagonal), and $k$ source–sink pairs $(s_\mu, t_\mu)$ with demands $D_\mu \ge 0$. Suppose some commodity has $D_\mu > 0$ and $s_\mu \ne t_\mu$. Then there is a set $S \subseteq V$ with $\mathrm{Dem}(S) > 0$ and
--   $$\frac{\mathrm{Cap}(S)}{\mathrm{Dem}(S)} \le C_0 \log(\max(k,2)) \cdot \mathrm{maxflow}(N).$$
--
--   Here $\mathrm{Cap}(S)$ is the total capacity of the edges leaving $S$, $\mathrm{Dem}(S)$ the total demand of the pairs separated by $S$, and $\mathrm{maxflow}(N)$ the largest $\lambda$ such that $\lambda D_\mu$ units of every commodity $\mu$ can be routed simultaneously within the capacities. Since every cut satisfies $\mathrm{maxflow} \le \mathrm{Cap}(S)/\mathrm{Dem}(S)$, the theorem says that the gap between the concurrent maximum multicommodity flow and the sparsest cut is $O(\log k)$, where $k$ is the number of commodities and not the number of vertices.
--
--   This is the main theorem of the paper. For a single commodity the max-flow min-cut theorem gives equality; for an expander with all-pairs unit demands the gap is of order $\log n$, so the logarithmic factor cannot be removed.
--
--   **Formalization Note** The paper asserts a deterministic polynomial-time algorithm that finds $S$; the statement asserts only the existence of $S$. The paper writes $O(\log k)$; the statement asserts an absolute constant $C_0$, quantified before the network, and uses $\log(\max(k,2))$ so that $k = 1$ is covered with the same constant. The inequality is cross-multiplied: $\mathrm{Cap}(S) \le C_0 \log(\max(k,2))\,\mathrm{maxflow}(N)\,\mathrm{Dem}(S)$. The hypothesis on some commodity is what makes some $\mathrm{Dem}(S)$ positive and maxflow finite.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 226, Theorem 4.1

import Mathlib
import Definitions.Def_GeometryOfGraphs_FlowCut_Network
import Definitions.Def_GeometryOfGraphs_FlowCut_Maxflow

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- Theorem 4.1 (p. 226), existence form: there is an absolute constant `C₀ > 0` such that every
multicommodity flow network with `k` source–sink pairs, at least one of which has positive demand and
distinct endpoints, has a vertex set `S` with `Dem(S) > 0` and
`Cap(S) / Dem(S) ≤ C₀ · log (max k 2) · maxflow` (stated cross-multiplied). The paper's `O(log k)`
is `C₀ · log (max k 2)`; the deterministic polynomial-time algorithm is not stated. -/
theorem theorem_4_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (N : Network V),
        (∃ μ, 0 < N.D μ ∧ N.s μ ≠ N.t μ) →
        ∃ S : Finset V, 0 < N.Dem S ∧
          N.Cap S ≤ C₀ * Real.log (max (N.k : ℝ) 2) * N.maxflow * N.Dem S := by sorry

end GeometryOfGraphs.FlowCut
