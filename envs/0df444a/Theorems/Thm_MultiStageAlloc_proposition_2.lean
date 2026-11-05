-- Prove2me | Theorems.Thm_MultiStageAlloc_proposition_2
-- name    : MultiStageAlloc.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:40.741003+00:00
-- url     : https://prove2.me/theorems/ea8d7145-2547-4600-aedb-33dff3053807
-- title:
--   Proposition 2 (corrected: Saturation only where $c>0$) — stage-wise structural decomposition
-- statement:
--   Fix $k\in[K-1]$, levels $y\in[0,1]^V$ and an optimal solution $x^*$ of the stage program, and consider its pairs $(U^{(l)}_k,V^{(l)}_k)$, $l\in[0:L_k]$. Then:
--
--   1. **Uniformity.** Every $j\in V^{(l)}_k$ has price $w_j\bigl(1-f_k(\text{level of }j)\bigr)=c^{(l)}_k$.
--   2. **Monotonicity.** For all $l,l'$, there is no edge of $E_k$ between $U^{(l)}_k$ and $V^{(l')}_k$ if $c^{(l)}_k<c^{(l')}_k$.
--   3. **Saturation.** For $l\in[L_k]$ with $c^{(l)}_k>0$, every online vertex $i\in U^{(l)}_k$ is fully matched: $\sum_jx^*_{ij}=1$.
--   4. $c^{(0)}_k=0$ and $c^{(l)}_k\ge 0$ for all $l$.
--
--   Here $c^{(l)}_k=0$ on a component without offline vertices. This decomposition is what lets the proof of Theorem 1 split the primal value among online and offline dual variables.
--
--   Differences from the source:
--   - generalization: capacities n_j = 1 "without the loss of generality" (p.12), and Algorithm 1 printed only for n_j = 1 → every real n_j > 0, with normalized levels y_j + Σ_i x_ij / n_j and the coefficient n_j in the regularizer and in the dual objective; reason: at n_j = 1 this is the printed text character for character, so the statement specializes to the source
--   - generalization: |U_k| ≥ 1 (p.12) → a batch may be empty, and U, V may be empty; reason: instances with nonempty batches are a subclass, and nothing in the proof uses nonemptiness
--   - reading: no cardinality assumption on U and V is printed → U and V are finite (Fintype); reason: the program and the LP are finite sums on the page, and footnote 8 and "no further assumptions" concern batch sizes
--   - encoding: x_k ∈ ℝ^{E_k} → x : U → V → ℝ vanishing off E_k; reason: sums over U and V are then the printed sums over E_k; same instances
--   - reading: "the optimal solution" of the stage program → every optimal solution; reason: the optimum need not be unique (p.17 "unique" is a slip: two online vertices sharing one offline vertex give several optima), and every optimum is the strongest reading
--   - generalization: y is the current vector of levels of Algorithm 1 → any y ∈ [0,1]^V; reason: the levels of a run lie in [0,1], so the source case is an instance, and the proof uses nothing else about y
--   - correction: Saturation for every l ∈ [L_k], and c^(l) defined only through an offline vertex → Saturation for l ∈ [L_k] with c^(l) > 0, and c^(l) = 0 on a component with no offline vertex; reason: printed false: K = 2, k = 1, V = {v}, w_v = 1, U₁ = {a, b}, x_av = 1, x_bv = 0 is optimal and b is an unmatched isolated component; and w_v = 0, U₁ = {a}, x_av = 1/2 is optimal with a unsaturated in a zero-price component (both proved in the sanity file)
--   - generalization: clauses 1–3 → also c^(0) = 0 and c^(l) ≥ 0; reason: p.21 states "0 = c^(0)_k < c^(1)_k < …" after merging equal values, and the merge is not needed for these two facts
--   - encoding: the pairs as a list indexed by l ∈ [0 : L_k] → an option on the connected components of the induced graph, none being l = 0; reason: the page constructs the same partition; no extra index order is asserted, since the merge of equal c on p.21 is a proof convenience
--   - encoding: Uniformity as equality of the prices of j, j′ ∈ V^(l), with common value c^(l) → every j ∈ V^(l) has price pairPrice l, the price of a vertex of the pair picked by choice; reason: the same statement, since the picked vertex lies in V^(l)
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Proposition 2, pp.20–21

import Mathlib
import Definitions.Def_MultiStageAlloc_Decomposition

namespace MultiStageAlloc

/-- **Proposition 2 (Stage-wise Structural Decomposition), corrected: Saturation only where `c > 0`.**
Feng & Niazadeh, arXiv:2211.16581v1, pp.20–21, for any `k ∈ [K - 1]`, levels `y ∈ [0, 1]^V` and
optimal solution `x` of (P^VWM_k).

The conjuncts: (1) Uniformity, every `j ∈ V^(l)_k` has price `c^(l)_k`; (2) Monotonicity, no edge
between `U^(l)_k` and `V^(l')_k` if `c^(l)_k < c^(l')_k`; (3) Saturation, every online vertex of a
component with `c^(l)_k > 0` is fully matched; and `0 = c^(0)_k ≤ c^(l)_k`, as used on p.21.

**Formalization Note.** The printed clause (3) has no `c > 0`, and is false: an online vertex with no
allocation is a component of its own, for which `c` is undefined, and a zero-weight component may be
unsaturated. See `pairPrice` for `c = 0` on a component with no offline vertex. -/
theorem proposition_2 {U V : Type*} [Fintype U] [Fintype V] {K : ℕ} (I : Instance U V K)
    (k : ℕ) (hk1 : 1 ≤ k) (hkK : k < K) (y : V → ℝ) (hy : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1)
    (x : U → V → ℝ) (hx : IsStageOptimal I k y x) :
    (∀ (l : PairIndex I k y x), ∀ j ∈ pairV I k y x l,
      levelPrice I k y x j = pairPrice I k y x l) ∧
    (∀ (l l' : PairIndex I k y x), pairPrice I k y x l < pairPrice I k y x l' →
      ∀ i ∈ pairU I k y x l, ∀ j ∈ pairV I k y x l', ¬ I.edge i j) ∧
    (∀ C : Component I k y x, 0 < pairPrice I k y x (some C) →
      ∀ i ∈ pairU I k y x (some C), ∑ j, x i j = 1) ∧
    pairPrice I k y x none = 0 ∧
    ∀ l : PairIndex I k y x, 0 ≤ pairPrice I k y x l := by sorry

end MultiStageAlloc
