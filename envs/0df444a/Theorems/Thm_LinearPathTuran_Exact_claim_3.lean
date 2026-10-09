-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_claim_3
-- name    : LinearPathTuran.Exact.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:46.056602+00:00
-- url     : https://prove2.me/theorems/06027fe4-4571-4966-ab6b-9047796a7370
-- title:
--   Claims 2–3, pp. 10–11 — a near-extremal ℙ_{2t+2}-free family has a t-set S joined in the kernel graph to n − O(√n) vertices
-- statement:
--   Let $k\ge 4$, $t\ge 1$ and $c_3\ge 0$. There are $C$ and $n_0$, depending on $k,t,c_3$, such that for every $n\ge n_0$ the following holds. Let $\mathcal F\subseteq\binom{[n]}{k}$ contain no $\mathbb P^{(k)}_{2t+2}$ and satisfy
--   $$|\mathcal F|\ge t\binom{n-1}{k-1}-c_3\,n^{k-2}.$$
--   Then there are a set $S\subseteq[n]$ with $|S|=t$ and a set $W\subseteq[n]\setminus S$ with
--   $$|W|\ge n-C\sqrt n$$
--   such that for every $x\in S$ and $w\in W$, $\deg^*_{\mathcal F}(\{x,w\})\ge s=k(2t+2)$, i.e. $xw$ is an edge of the kernel graph of $\mathcal F$ with threshold $s$.
--
--   This is the stability step of §5: a near-extremal family already looks like the extremal construction around a $t$-set $S$.
--
--   **Formalization Note** In the paper $S=\{x_1,\dots,x_t\}$ consists of the $t$ vertices of largest out-degree in the kernel multigraph of a canonical partition (Claim 2: $d_1,\dots,d_t\ge n-O(n^{1/2})$), and $W$ is the largest set joined to all of $S$ (Claim 3: $|W|\ge n-O(n^{1/2})$). Stand-alone, $S$ is existentially quantified, $O(n^{1/2})$ is $C\sqrt n$, and any $W$ with the size bound replaces the maximum one. The hypothesis $|\mathcal F|\ge t\binom{n-1}{k-1}-c_3n^{k-2}$ is the paper's standing assumption of §5 (p. 9).
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 9 (§5, the constant c₃), pp. 10–11 (Claim 2 and Claim 3)

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Claims 2–3, pp. 10–11, stand-alone: a near-extremal `ℙ_{2t+2}`-free family has a `t`-set `S`
and a set `W` of size `n - O(√n)` outside `S` with every pair `x ∈ S`, `w ∈ W` an edge of the
kernel graph with threshold `k(2t + 2)`. -/
theorem claim_3 (k t : ℕ) (hk : 4 ≤ k) (ht : 1 ≤ t) (c₃ : ℝ) (hc₃ : 0 ≤ c₃) :
    ∃ (C : ℝ) (n₀ : ℕ), ∀ n ≥ n₀, ∀ 𝓕 : Finset (Finset (Fin n)),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k → ¬ ContainsLinearPath 𝓕 (2 * t + 2) →
      (t : ℝ) * ((n - 1).choose (k - 1) : ℝ) - c₃ * (n : ℝ) ^ (k - 2) ≤ #𝓕 →
      ∃ S W : Finset (Fin n), #S = t ∧ Disjoint S W ∧ (n : ℝ) - C * Real.sqrt n ≤ #W ∧
        ∀ x ∈ S, ∀ w ∈ W, (kernelGraph 𝓕 (k * (2 * t + 2))).Adj x w := by sorry

end LinearPathTuran.Exact
