-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_11
-- name    : NAMatchEst.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:58:21.369175+00:00
-- url     : https://prove2.me/theorems/e9f95e55-2e96-4ca4-b5e1-01be306bf28b
-- title:
--   Lemma 3.11 — size and sandwich guarantees of the pilot
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. We are in the main case $k>\alpha^2$ and $n$ is sufficiently large.
--
--   The pilot scheme of Definition 3.10 uses $O(nkL/\alpha^3)$ queries and always (for every graph and every outcome) satisfies $|H|\le k/32$. With probability at least $1-n^{-30}$ it also satisfies
--
--   $$
--   V_1^H\subseteq H\subseteq\{v\in V: d_U(v)>16\alpha^2\}\subseteq V_1 . \qquad (21)
--   $$
--
--   In particular, $V_1^H\subseteq H\subseteq V_1$ with probability at least $1-n^{-30}$.
--
--   **Formalization Note** One constant for the $O(\cdot)$ and one threshold for "sufficiently large", both chosen before $n$, $\alpha$, $k$; the cost bound holds for every seed.
--
--   Differences from the source:
--   - encoding: a simple undirected graph G on n vertices with fixed adjacency-list orderings → G : AdjList n on Fin n (ordered, duplicate-free, symmetric, loopless lists); reason: every simple graph with every ordering is an AdjList; same instances
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - reading: O(·) → one constant D chosen before n, α and k; reason: the uniform reading of a universal constant
--   - generalization: identical oracle queries may be answered once (p.20) → every occurrence of a query is charged; reason: a bound on the charged count implies the source's bound
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.11, p.27 (PDF 31)

import Mathlib
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_run
import Definitions.Def_NAMatchEst_RandAlg_prob
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_dU
import Definitions.Def_NAMatchEst_V1H
import Definitions.Def_NAMatchEst_pilot

namespace NAMatchEst

/-- **Lemma 3.11 (Size and sandwich guarantees).** The pilot scheme uses `O(nkL/α³)` queries and
always satisfies `|H| ⩽ k/32`. With probability at least `1 − n^{−30}`, it also satisfies
`V₁^H ⊆ H ⊆ {v ∈ V : d_U(v) > 16α²} ⊆ V₁` (21). In particular, `V₁^H ⊆ H ⊆ V₁` with probability
at least `1 − n^{−30}`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.11, p.27 (PDF 31), with the pilot of Definition 3.10, p.26 (PDF 30), in the main
case `k > α²` of the standing setup of §3.2, p.19 (PDF 23), including "n exceeds a sufficiently
large universal constant" (used in the proof: "n is sufficiently large, s0 ⩽ 2nL/α²").

**Formalization Note** One constant `D` and one threshold `N₀`, chosen before `n`, `α`, `k`.
"Always" is: for every seed and every input graph. -/
theorem lemma_3_11 : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    (pilot n α k).CostLE (D * n * k * L n / α ^ 3) ∧
    ∀ G : AdjList n,
      (∀ ω, (((pilot n α k).run G ω).card : ℝ) ≤ k / 32) ∧
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (pilot n α k).prob G (fun H =>
        V1H G α k ⊆ H ∧ H ⊆ Finset.univ.filter (fun v => 16 * α ^ 2 < (dU G α k v : ℝ)) ∧
          Finset.univ.filter (fun v => 16 * α ^ 2 < (dU G α k v : ℝ)) ⊆ V1 G α k) ∧
      1 - (n : ℝ) ^ (-30 : ℝ) ≤ (pilot n α k).prob G (fun H => V1H G α k ⊆ H ∧ H ⊆ V1 G α k) := by sorry

end NAMatchEst
