-- Prove2me | Theorems.Thm_NMAffExt_LBP_lemma_4_6
-- name    : NMAffExt.LBP.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:29:46.528164+00:00
-- url     : https://prove2.me/theorems/2eb6f047-73b3-49e9-b4a9-56c25ac5f27b
-- title:
--   Lemma 4.6 — a full weakly read-once program of $O(ns)$ vertices computing $P$, with a cut of at most $2s$ nodes at query rank $k$
-- statement:
--   There is a universal constant $C$ such that the following holds. Let $P$ be a weakly read-once linear branching program on $n$ bits with $s$ vertices, and let $1\le k<n$. There is a full weakly read-once linear branching program $P'$ on $n$ bits with at most $C\,n\,s$ vertices that computes $P$ ($P'(x)=P(x)$ for all $x$), and a set $V$ of at most $2s$ of its nodes, such that:
--
--   1. every computation of $P'$ reaches exactly one node of $V$;
--   2. for each $v\in V$, every path from the source to $v$ has the same $k$-dimensional query span $W_v$;
--   3. whenever, for each $v\in V$, the rows of $Q_v\in\mathbb F_2^{k\times n}$ form a basis of $W_v$, there are sets $A_v\subseteq\mathbb F_2^k$ such that an input $x$ reaches $v$ exactly when $Q_vx\in A_v$, the reaching probability is $\Pr_{x\sim U_n}[x\text{ reaches }v]=p_v=|A_v|/2^k$, and
--   $$\sum_{v\in V}\frac{|A_v|}{2^k}=1.$$
--
--   This normalization ([GPT22, Lemma 16] with the cut size tracked) is the structural input to the correlation bound of Theorem 4.8.
--
--   Differences from the source:
--   - encoding: "The normalized program has $O(ns)$ vertices" → `∃ C : ℝ` placed before all of `n s k P`, with at most `C * n * s` vertices; reason: an explicit universal constant for the $O(\cdot)$.
--   - encoding: "Its reaching probability is $p_v=|A_v|/2^k$" → the number of inputs reaching $v$ divided by $2^n$ equals $|A_v|/2^k$; reason: probability under $U_n$ as a count.
--   - reading: "The cut may contain original nodes, inserted nodes, and copies of sinks" → not a clause of the Lean statement ($V$ is any set of nodes of $P'$); reason: the sentence describes the construction and asserts nothing about the conclusion.
-- source:
--   Xin Li, Yan Zhong, Non-Malleable Affine Extractors with Small Error and Complexity Lower Bounds, arXiv:2610.02407 (version of 2026-11-02, sha256 e80dad4d…), p. 57 (PDF 59), Lemma 4.6

import Mathlib
import Definitions.Def_NMAffExt_LBP_Program

open Matrix

namespace NMAffExt.LBP

/-- **Lemma 4.6.** There is a universal constant `C` such that every size-`s` weakly read-once
linear branching program `P` on `n` bits and every `1 ≤ k < n` admit a full weakly read-once program
`P'` computing `P`, with at most `C·n·s` vertices, and a set `V` of at most `2s` of its nodes such that
(1) every computation reaches exactly one node of `V`; (2) for each `v ∈ V` every path reaching `v`
has the same `k`-dimensional query span `W v`; (3) if the rows of `Q v` form a basis of `W v`, an
input reaches `v` exactly when `Q v x ∈ A v`, the reaching probability is `|A v| / 2^k`, and these
probabilities sum to one over `V`. -/
theorem lemma_4_6 :
    ∃ C : ℝ, ∀ (n s k : ℕ) (P : Program n s), P.IsWeaklyReadOnce → 1 ≤ k → k < n →
      ∃ (s' : ℕ) (P' : Program n s'),
        P'.IsWeaklyReadOnce ∧ P'.IsFull ∧ (∀ x, P'.eval x = P.eval x) ∧
        (s' : ℝ) ≤ C * n * s ∧
        ∃ (V : Finset (Fin s')) (W : Fin s' → Submodule (ZMod 2) (Fin n → ZMod 2)),
          V.card ≤ 2 * s ∧
          (∀ x : Fin n → ZMod 2, ∃! v, v ∈ V ∧ P'.Reaches x v) ∧
          (∀ v ∈ V, Module.finrank (ZMod 2) (W v) = k ∧
            ∀ l, P'.IsPathTo l v → P'.pathSpan l = W v) ∧
          (∀ Q : Fin s' → Matrix (Fin k) (Fin n) (ZMod 2), (∀ v ∈ V, RowsBasis (Q v) (W v)) →
            ∃ A : Fin s' → Finset (Fin k → ZMod 2),
              (∀ v ∈ V, ∀ x, P'.Reaches x v ↔ Q v *ᵥ x ∈ A v) ∧
              (∀ v ∈ V, (Nat.card {x : Fin n → ZMod 2 // P'.Reaches x v} : ℝ) / 2 ^ n =
                ((A v).card : ℝ) / 2 ^ k) ∧
              ∑ v ∈ V, ((A v).card : ℝ) / 2 ^ k = 1) := by sorry

end NMAffExt.LBP
