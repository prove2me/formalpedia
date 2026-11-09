-- Prove2me | Theorems.Thm_HypRecov_lemma_6_1
-- name    : HypRecov.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:55.663322+00:00
-- url     : https://prove2.me/theorems/25e40875-a8d4-4b9e-addd-708190fb37f1
-- title:
--   Lemma 6.1 — connectivity around a full component
-- statement:
--   Throughout, $H$ is a simple $r$-uniform hypergraph on $V=\{0,\dots,n-1\}$ with $r\ge 2$, $k\ge 3$, $K=k-1$ and $M=2^{\lceil\log_2 k\rceil-1}$ (so $M\le K<2M$); $D\subseteq E(H)$ is a set of recovered edges and $J=H-D$ the residual hypergraph; $P_0$ is a safe base partition. A **small cut** is a set $S$ with $\mathrm{cut}_H(S)<k$. The current partition $P$ is safe and coarsens $P_0$, and $G$ is the block graph of $J$ and $P$ (current blocks filled in, plus residual pairs).
--
--   Suppose no edge qualifies for completion. Let $R$ be a clique of $G$ with $|R|<r$ and $L$ a component of $G-R$ with $N_G(L)=R$, and set $Q=L\cup R$. Then the graph $A_Q$ on $Q$, which joins two vertices in the same current block and two vertices with at least one in $L$ and residual codegree at least $M$, is connected.
--
--   Differences from the source:
--   - reading: cache records, edge labels and available complete lists (Proposition 4.1) → the true residual quantities avail, knownMembers, envelope, numPoints; reason: the arguments are deterministic on the cache success event (p.9), where every value read is the true one and labels are injective on T_K (paper.md decision 7)
--   - encoding: a component L of G − R; A_Q on Q → IsCompOf; auxGraph induced on L ∪ R; reason: Lean convention
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 6.1, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_Safe
import Definitions.Def_HypRecov_envelope
import Definitions.Def_HypRecov_IsCompOf
import Definitions.Def_HypRecov_auxGraph

namespace HypRecov

/-- **Lemma 6.1 (Connectivity around a full component).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 6.1, p.13
(PDF p.14): "Suppose the completion rule (4) has no qualifying edge spanning current blocks. Let R be a
clique of G with |R| < r, and let L be a component of G − R with N_G(L) = R. Set Q = L ∪ R. On Q,
define the proof-only graph A_Q by including: 1. all current-block clique edges restricted to Q.
2. every pair with at least one endpoint in L whose true residual codegree is at least M. The first
clause includes all pairs within a current block. The second adds cross-block pairs, whose codegrees
are available in the cache. Then A_Q is connected."

Setting (§4–§6.1): `H` simple `r`-uniform, `2 ≤ r`, `k ≥ 3`, `M = 2^{⌈log₂ k⌉−1}`; `D ⊆ E(H)`,
`J = H − D`; base partition `P₀` and current partition `P` coarsening it, `P` safe; `G` is the block
graph of `J` and `P`.

**Formalization Note.** Stated on true data (paper.md decision 7). `A_Q` is `auxGraph`, and the
conclusion is about its subgraph induced on `Q`. -/
theorem lemma_6_1 {n : ℕ} (E D : Finset (Finset (Fin n))) (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (hE : ∀ e ∈ E, e.card = r) (hD : D ⊆ E) (P₀ P : Fin n → Fin n) (hco : Coarsens P₀ P)
    (hP : Safe E k P) (hterm : CompletionTerminal r (E \ D) P₀ P (Mpow k))
    (R L : Finset (Fin n)) (hR : (blockGraph (E \ D) P).IsClique (R : Set (Fin n)))
    (hRr : R.card < r) (hL : IsCompOf (blockGraph (E \ D) P) R L)
    (hN : nbhd (blockGraph (E \ D) P) L = R) :
    ((auxGraph (E \ D) P (Mpow k) L (L ∪ R)).induce ((L ∪ R : Finset (Fin n)) : Set (Fin n))).Connected
    := by sorry

end HypRecov
