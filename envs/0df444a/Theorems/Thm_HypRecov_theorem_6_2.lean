-- Prove2me | Theorems.Thm_HypRecov_theorem_6_2
-- name    : HypRecov.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:38.324755+00:00
-- url     : https://prove2.me/theorems/eeaa108c-d2b2-4646-8518-3f3c149fe34d
-- title:
--   Theorem 6.2 — safe contraction of small minimal clique separators
-- statement:
--   Throughout, $H$ is a simple $r$-uniform hypergraph on $V=\{0,\dots,n-1\}$ with $r\ge 2$, $k\ge 3$, $K=k-1$ and $M=2^{\lceil\log_2 k\rceil-1}$ (so $M\le K<2M$); $D\subseteq E(H)$ is a set of recovered edges and $J=H-D$ the residual hypergraph; $P_0$ is a safe base partition. A **small cut** is a set $S$ with $\mathrm{cut}_H(S)<k$. The current partition $P$ is safe and coarsens $P_0$, and $G$ is the block graph of $J$ and $P$ (current blocks filled in, plus residual pairs).
--
--   Suppose no edge qualifies for completion, and let $R$ be a nonempty minimal clique separator of $G$ with $|R|<r$. Then
--
--   1. every set $S$ separating two vertices of $R$ has $\mathrm{cut}_H(S)\ge k$;
--   2. merging all current blocks that meet $R$ gives a safe partition.
--
--   Differences from the source:
--   - reading: minimal separator: inclusion-minimal for some pair of separated vertices → R a clique of G with two distinct full components of G − R; reason: the paper prints this form as equivalent (p.13; paper.md decision 10)
--   - reading: "Its current blocks may be merged" → merging the current blocks meeting R yields a safe partition; reason: safety is what licenses a merger (§4, p.8)
--   - reading: cache records, edge labels and available complete lists (Proposition 4.1) → the true residual quantities avail, knownMembers, envelope, numPoints; reason: the arguments are deterministic on the cache success event (p.9), where every value read is the true one and labels are injective on T_K (paper.md decision 7)
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 6.2, p.14 (PDF p.15)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_Safe
import Definitions.Def_HypRecov_envelope
import Definitions.Def_HypRecov_IsCompOf

namespace HypRecov

/-- **Theorem 6.2 (Safe contraction of small minimal clique separators).** Zhang, Chen, Shen,
*Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256
719dcfff…), Theorem 6.2, p.14 (PDF p.15): "At a completion-terminal state, every nonempty minimal
clique separator R of G with |R| < r has the following property: every cut of H separating two
vertices of R has size at least k. Its current blocks may be merged."

Setting as in Lemma 6.1. Both sentences: (a) every `S` separating two vertices of `R` has
`cut_H(S) ≥ k`; (b) merging all current blocks that meet `R` gives a safe partition.

**Formalization Note.** Minimal clique separators in the two-full-components form that p.13 prints as
equivalent (`IsMinCliqueSep`). -/
theorem theorem_6_2 {n : ℕ} (E D : Finset (Finset (Fin n))) (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (hE : ∀ e ∈ E, e.card = r) (hD : D ⊆ E) (P₀ P : Fin n → Fin n) (hco : Coarsens P₀ P)
    (hP : Safe E k P) (hterm : CompletionTerminal r (E \ D) P₀ P (Mpow k))
    (R : Finset (Fin n)) (hRne : R.Nonempty) (hRr : R.card < r)
    (hR : IsMinCliqueSep (blockGraph (E \ D) P) R) :
    (∀ S : Finset (Fin n), (∃ u ∈ R, ∃ v ∈ R, u ∈ S ∧ v ∉ S) → k ≤ cut E S) ∧
    ∀ P' : Fin n → Fin n, IsMergeOf P R P' → Safe E k P' := by sorry

end HypRecov
