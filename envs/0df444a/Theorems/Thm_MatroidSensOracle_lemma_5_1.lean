-- Prove2me | Theorems.Thm_MatroidSensOracle_lemma_5_1
-- name    : MatroidSensOracle.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:10.178849+00:00
-- url     : https://prove2.me/theorems/e5796bf0-53f4-40b0-8402-05b1eafcb9ff
-- title:
--   Lemma 5.1 (corrected: $k-\lambda$ bypass edges $s^*\to t^*$, not self-loops): $\lambda$ edge-disjoint paths iff a $k$-packing of common bases of $M_{\mathrm{out}}$, $M_{\mathrm{in}}$
-- statement:
--   Let $H$ be a directed multigraph on a finite set of $N$ vertices with finitely many edges, a source $s^*$ and a sink $t^*\ne s^*$, and let $k\ge1$ and $\lambda\le k$ be such that $s^*$ has out-degree $\lambda$ and $t^*$ has in-degree $\lambda$. Form the gadget by adding $k$ self-loops at every vertex other than $s^*,t^*$ and $k-\lambda$ parallel edges from $s^*$ to $t^*$. Then $H$ contains $\lambda$ edge-disjoint $(s^*,t^*)$-paths if and only if some set $S$ of $k(N-1)$ gadget edges can be partitioned into $k$ bases of $M_{\mathrm{out}}$ and also (possibly differently) into $k$ bases of $M_{\mathrm{in}}$.
--
--   It turns bounded flow into $k$-intersection-packing of two partition matroids.
--
--   Differences from the source:
--   - correction: to vertices s∗ and t∗ we add k − λ zero-cost self-loops → k − λ parallel edges s∗ → t∗ (bypass edges); reason: as printed the lemma is false for λ < k: an s∗-loop has the zero column in A_in and a t∗-loop in A_out, so no basis contains them; for k = 1, λ = 0, two vertices, no edges, H has 0 edge-disjoint paths but no 1-element set is a basis of both (the k = 2, λ = 1 instance is checked in Lean)
--   - reading: M_out: every v ∈ V_H \ {t∗} has at most one outgoing edge in S; represented by A_out → no edge of S leaves t∗ and every vertex has at most one outgoing edge in S (independence of the columns of A_out); M_in symmetrically; reason: the sentence and the matrix differ only when an edge leaves t∗ or enters s∗; the matrix gives the printed rank N − 1
--   - encoding: zero-cost self-loops; edge-disjoint (s∗, t∗)-paths → costs omitted; paths as edge lists with no repeated vertex, pairwise edge-disjoint; reason: costs play no role in the lemma; paths as in §2
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Lemma 5.1, p.25 (PDF p.28), with the construction of §5.1, p.25

import Mathlib
import Definitions.Def_MatroidSensOracle_Gadget

set_option autoImplicit false

namespace MatroidSensOracle

open CombOpt.MinCostFlow

/-- **Lemma 5.1 (corrected: k − λ bypass edges s∗ → t∗ instead of self-loops at s∗, t∗).**
Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), p.25 (PDF p.28): "The
directed multigraph H contains λ edge-disjoint (s∗, t∗)-paths if and only if there exists a set
S ⊆ E_H of size k(N − 1) that can be partitioned into k bases of M_out as well as M_in (the
partitionings may differ)."

**Formalization Note.** `H` is a directed multigraph on the finite vertex type `V` (`N = |V|`) with
finitely many edges, `s∗ ≠ t∗`, out-degree of `s∗` and in-degree of `t∗` both `λ ≤ k`, `k ≥ 1`. The
graph of the lemma is the corrected gadget `gadget H s∗ t∗ k (k − λ)`: `k` self-loops at each
`v ∉ {s∗, t∗}` and `k − λ` parallel edges `s∗ → t∗` (as printed, with `k − λ` self-loops at `s∗` and
at `t∗`, the lemma is false for `λ < k`: those loops are loops of `M_in` and `M_out`). `M_out` and
`M_in` are the matroids of the matrices `A_out`, `A_in` (`IndepOut`, `IndepIn`); bases are maximal
independent sets. -/
theorem lemma_5_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (H : Digraph V E) (s t : V) (hst : s ≠ t) (k lam : ℕ) (hk : 1 ≤ k) (hlam : lam ≤ k)
    (hout : (Finset.univ.filter fun e => H.tail e = s).card = lam)
    (hin : (Finset.univ.filter fun e => H.head e = t).card = lam) :
    HasEdgeDisjointPaths H s t lam ↔
      ∃ S : Finset (GadgetEdge V E s t k (k - lam)), S.card = k * (Fintype.card V - 1) ∧
        SplitsInto (Maximal (IndepOut (gadget H s t k (k - lam)) t)) k S ∧
        SplitsInto (Maximal (IndepIn (gadget H s t k (k - lam)) s)) k S := by sorry

end MatroidSensOracle
