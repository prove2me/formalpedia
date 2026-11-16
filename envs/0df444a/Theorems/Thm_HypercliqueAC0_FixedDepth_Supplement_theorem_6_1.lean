-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_Supplement_theorem_6_1
-- name    : HypercliqueAC0.FixedDepth.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:07.272948+00:00
-- url     : https://prove2.me/theorems/0b1d3d03-a5c7-4141-bf65-8f4530d02dbc
-- title:
--   Theorem 6.1: depth-$h$ circuits for $k$-Clique with $k_0\le k\le n^{1/(h-1)-\varepsilon}$ need more than $n^{ck}$ gates
-- statement:
--   Let $k\text{-}\mathsf{Clique}_n$ be the Boolean function that receives one bit $x_e$ for every pair $e$ of the vertex set $[n]$ and outputs one exactly when the graph $\{e: x_e=1\}$ contains a clique on $k$ vertices. A depth-$h$ circuit is a De Morgan circuit (unbounded fan-in AND and OR gates over literals and constants) of depth at most $h$, and its gate size $G(C)$ is the number of its noninput gates.
--
--   For every integer $h\ge2$ and every real $\varepsilon>0$ there are integers $k_0,n_0$ and a real $c>0$ such that, for every $n\ge n_0$ and every integer $k$ with
--
--   $$k_0\le k\le n^{1/(h-1)-\varepsilon},$$
--
--   every depth-$h$ circuit $C$ computing $k\text{-}\mathsf{Clique}_n$ satisfies
--
--   $$G(C)>n^{ck}.$$
--
--   The constants depend only on $h$ and $\varepsilon$. Compared with the hyperclique goal at $r=2$, the range of $k$ is wider by one layer of the circuit: $n^{1/(h-1)}$ instead of $n^{1/h}$.
--
--   **Formalization Note** $k\text{-}\mathsf{Clique}_n$ is the published `hyperclique n 2 k` on the pair type `Edge n 2`. No restriction $\varepsilon<1/(h-1)$ is added; for larger $\varepsilon$ the range of $k$ may be empty, as in the source.
--
--   Differences from the source:
--   - encoding: $[n]=\{1,\ldots,n\}$ and its pairs → $\mathrm{Fin}\,n$ with the edge subtype of cardinality $2$; reason: a relabeling bijection preserves every graph and every circuit instance
--   - encoding: integer thresholds $k_0,n_0$ and integers $h,k,n$ → natural numbers, with real casts before division and exponentiation; reason: all are lower thresholds or counts, and a natural threshold can dominate any integer threshold without changing the conclusion
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.20 (PDF p.22), Theorem 6.1

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_HypercliqueAC0_FixedDepth_Hypergraphs

noncomputable section

namespace HypercliqueAC0.FixedDepth.Supplement
open HypercliqueAC0.FixedDepth

/-- Theorem 6.1, p. 20 (PDF 22). `k-Clique_n` is `hyperclique n 2 k` on the edge variables
`Edge n 2`; a depth-`h` circuit is a De Morgan circuit of depth at most `h`, and its gate size is
the length of its gate list. The constants `k₀, n₀, c` depend only on `h` and `ε`; the bound is
strict. No restriction `ε < 1/(h−1)` is added. -/
theorem theorem_6_1 (h : ℕ) (hh : 2 ≤ h) (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ n₀ : ℕ, ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k₀ ≤ k →
        (k : ℝ) ≤ (n : ℝ) ^ (1 / ((h : ℝ) - 1) - ε) →
        ∀ C : MantriCVQ.ACCircuit (Edge n 2), C.depth ≤ h →
          (∀ x, C.eval x = hyperclique n 2 k x) →
          (n : ℝ) ^ (c * (k : ℝ)) < (C.gates.length : ℝ) := by sorry

end HypercliqueAC0.FixedDepth.Supplement
