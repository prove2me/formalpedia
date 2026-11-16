-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_Supplement_theorem_1_2
-- name    : HypercliqueAC0.FixedDepth.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:26.117613+00:00
-- url     : https://prove2.me/theorems/617b7599-7356-4ab8-a6cf-3d3f7938a30b
-- title:
--   Theorem 1.2: depth-$h$ circuits for $k$-Clique need $n^{\Omega(k)}$ gates for $3\le k\le n^{1/(h-1)-\varepsilon}$ and $n^{(1/4-o(1))k}$ gates for $k=n^{o(1)}$
-- statement:
--   Let $k\text{-}\mathsf{Clique}_n$ be the Boolean function of the $\binom n2$ edge bits of a graph on $[n]$ that outputs one exactly when the graph contains a clique on $k$ vertices. A depth-$h$ circuit is a De Morgan circuit of depth at most $h$, and $G(C)$ is its number of noninput gates. The theorem has two claims.
--
--   1. For every integer $h\ge2$ and every $\varepsilon>0$ there are $c>0$ and $n_0$, depending only on $h$ and $\varepsilon$, such that for every $n\ge n_0$ and every integer $k$ with $3\le k\le n^{1/(h-1)-\varepsilon}$, every depth-$h$ circuit $C$ computing $k\text{-}\mathsf{Clique}_n$ satisfies
--   $$G(C)\ge n^{ck}.$$
--   2. For every integer $h\ge2$ and every $\eta>0$ there are $\delta>0$ and thresholds $k_0,n_0$ such that for every $n\ge n_0$ and every integer $k$ with $k_0\le k\le n^{\delta}$, every depth-$h$ circuit $C$ computing $k\text{-}\mathsf{Clique}_n$ satisfies
--   $$G(C)\ge n^{(1/4-\eta)k}.$$
--
--   The first claim is the $n^{\Omega_{h,\varepsilon}(k)}$ bound over the whole range of $k$, including constant $k\ge3$. The second claim is the paper's statement that $n^{(1/4-o(1))k}$ gates are needed when $k\to\infty$ and $k=n^{o(1)}$, matching Rossman's exponent $k/4$ for constant $k$.
--
--   **Formalization Note** $k\text{-}\mathsf{Clique}_n$ is the published `hyperclique n 2 k` on `Edge n 2`. The second claim is written in uniform form: for every sequence $(n_i,k_i)$ with $k_i\to\infty$ and $\log k_i/\log n_i\to0$ it gives the $o(1)$ bound, and conversely, if the uniform form failed for some $\eta$, the counterexamples for $\delta=1/j$ and $k_0=n_0=j$, $j=1,2,\dots$, would form such a sequence violating the sequence form.
--
--   Differences from the source:
--   - encoding: $[n]=\{1,\ldots,n\}$ and its pairs → $\mathrm{Fin}\,n$ with the edge subtype of cardinality $2$; reason: a relabeling bijection preserves every graph and every circuit instance
--   - encoding: integers $h,k,n$ and the threshold for "sufficiently large $n$" → natural numbers, with real casts before division and exponentiation; reason: all are counts or lower thresholds, and a natural threshold can dominate any integer threshold
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
--   - reading: "$n^{\Omega_{h,\varepsilon}(k)}$ gates if $n$ is sufficiently large" → there exist $c>0$ and $n_0$ depending only on $h,\varepsilon$ with $n^{ck}\le G(C)$ for all $3\le k\le n^{1/(h-1)-\varepsilon}$; reason: the subscript of $\Omega$ names exactly $h,\varepsilon$, so $c$ is uniform in $k$ and $n$
--   - reading: "if $k$ tends to infinity and $k=n^{o(1)}$, then $n^{(1/4-o(1))k}$ gates" → for every $\eta>0$ there are $\delta>0$ and $k_0,n_0$ such that $k_0\le k\le n^{\delta}$, $n\ge n_0$ imply $n^{(1/4-\eta)k}\le G(C)$; reason: this uniform form is equivalent to the statement for all sequences with $k\to\infty$, $k=n^{o(1)}$ (see the Formalization Note)
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.4 (PDF p.6), Theorem 1.2; proof p.22 (PDF p.24)

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_HypercliqueAC0_FixedDepth_Hypergraphs

noncomputable section

namespace HypercliqueAC0.FixedDepth.Supplement
open HypercliqueAC0.FixedDepth

/-- Theorem 1.2, p. 4 (PDF 6), both claims. First claim: `n^{Ω_{h,ε}(k)}` is `n^{c k}` with
`c > 0` depending only on `h, ε`, for every `3 ≤ k ≤ n^{1/(h−1)−ε}` once `n ≥ n₀(h, ε)`.
Second claim ("if `k → ∞` and `k = n^{o(1)}`, then `n^{(1/4−o(1))k}` gates"), in its uniform
form: for every `η > 0` there are `δ > 0` and thresholds `k₀, n₀` such that every
`k₀ ≤ k ≤ n^δ`, `n ≥ n₀` forces `n^{(1/4−η)k}` gates. This is equivalent to the sequence reading. -/
theorem theorem_1_2 :
    (∀ h : ℕ, 2 ≤ h → ∀ ε : ℝ, 0 < ε →
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 3 ≤ k →
        (k : ℝ) ≤ (n : ℝ) ^ (1 / ((h : ℝ) - 1) - ε) →
        ∀ C : MantriCVQ.ACCircuit (Edge n 2), C.depth ≤ h →
          (∀ x, C.eval x = hyperclique n 2 k x) →
          (n : ℝ) ^ (c * (k : ℝ)) ≤ (C.gates.length : ℝ)) ∧
    (∀ h : ℕ, 2 ≤ h → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∃ k₀ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, k₀ ≤ k →
        (k : ℝ) ≤ (n : ℝ) ^ δ →
        ∀ C : MantriCVQ.ACCircuit (Edge n 2), C.depth ≤ h →
          (∀ x, C.eval x = hyperclique n 2 k x) →
          (n : ℝ) ^ ((1 / 4 - η) * (k : ℝ)) ≤ (C.gates.length : ℝ)) := by sorry

end HypercliqueAC0.FixedDepth.Supplement
