-- Prove2me | Theorems.Thm_GaussianSweep_theorem_8_1
-- name    : GaussianSweep.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:50.37529+00:00
-- url     : https://prove2.me/theorems/80143efd-2c0b-4b4c-824d-b924e6b9ae1a
-- title:
--   Theorem 8.1 — every graph of maximum degree 3 has $\mathrm{pw}(G) \le \frac{3}{4\pi}\arccos\frac56\, n + o(n)$
-- statement:
--   Every finite graph $G$ with maximum degree $\Delta(G) \le 3$ satisfies
--   $$
--   \mathrm{pw}(G) \le c_3\, n + o(n), \qquad c_3 = \frac{3}{4\pi}\arccos\frac{5}{6} \approx 0.13982,
--   $$
--   where $n = |V(G)|$. Following the paper's convention for remainders (Section 4.1), this means: there is a single function $\rho : \mathbb N \to \mathbb R$ with $\rho(n)/n \to 0$, depending on $n$ only and not on the graph, such that every graph $G$ with $\Delta(G) \le 3$ satisfies $\mathrm{pw}(G) \le c_3 n + \rho(n)$.
--
--   The graphs may be disconnected and have vertices of degree $0$, $1$ or $2$. The bound improves the constant $1/6$ of Fomin and Høie (2006), and by known relations it also bounds bisection width and cutwidth of graphs of maximum degree $3$; it also bounds treewidth.
--
--   **Formalization Note** A graph is a `SimpleGraph` on a finite vertex type, $n$ its cardinality, and $\Delta(G) \le 3$ is Mathlib's `maxDegree`. The remainder is quantified before the graph.
--
--   Differences from the source:
--   - encoding: a finite simple graph G → a SimpleGraph on a finite vertex type V (Fintype), n = card V; reason: every finite graph is isomorphic to one on a finite type; pathwidth and degrees are invariant
--   - encoding: pw(G) ≤ c₃n + o(n) → ∃ ρ : ℕ → ℝ with ρ(n)/n → 0 such that ∀ graphs, pw(G) ≤ c₃·card V + ρ(card V); reason: the paper's own definition of o(n) in Section 4.1, p.22
--   - encoding: pw(G) as an integer in a real inequality → (pathwidth G : ℝ), with pathwidth ℤ-valued; reason: the integer is compared in ℝ
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 8.1, p.45 (PDF p.47); Theorem 1.1(a), p.1 (PDF p.3); remainder convention Section 4.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_c3
open Filter Topology

namespace GaussianSweep

/-- Theorem 8.1 (maximum degree 3) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Theorem 8.1, p.45 (PDF p.47); Theorem 1.1(a), p.1
(PDF p.3)). Every graph `G` with `Δ(G) ≤ 3` satisfies `pw(G) ≤ c₃ n + o(n)`, where
`c₃ = (3/(4π)) arccos(5/6)`.

**Formalization Note** The remainder follows Section 4.1 (p.22): there is one function
`ρ : ℕ → ℝ` with `ρ(n)/n → 0`, chosen before the graph, such that every graph satisfies the bound
with `ρ(|V(G)|)`. A graph is a `SimpleGraph` on any finite vertex type `V`, `n = card V`; no
connectivity, regularity, minimum degree or girth is assumed. -/
theorem theorem_8_1 : ∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj], G.maxDegree ≤ 3 →
      (pathwidth G : ℝ) ≤ c3 * Fintype.card V + ρ (Fintype.card V) := by sorry

end GaussianSweep
