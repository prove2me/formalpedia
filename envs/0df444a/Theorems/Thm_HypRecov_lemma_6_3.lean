-- Prove2me | Theorems.Thm_HypRecov_lemma_6_3
-- name    : HypRecov.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:25.480849+00:00
-- url     : https://prove2.me/theorems/9094e256-4343-41d7-a261-c60bd4d1633e
-- title:
--   Lemma 6.3 — cuts exposed by deleting a block
-- statement:
--   Throughout, $H$ is a simple $r$-uniform hypergraph on $V=\{0,\dots,n-1\}$ with $r\ge 2$, $k\ge 3$, $K=k-1$ and $M=2^{\lceil\log_2 k\rceil-1}$ (so $M\le K<2M$); $D\subseteq E(H)$ is a set of recovered edges and $J=H-D$ the residual hypergraph; $P_0$ is a safe base partition. A **small cut** is a set $S$ with $\mathrm{cut}_H(S)<k$. The current partition $P$ is safe and coarsens $P_0$, and $G$ is the block graph of $J$ and $P$ (current blocks filled in, plus residual pairs).
--
--   Suppose completion and the small-minimal-separator contractions are saturated: no edge qualifies for completion, and every nonempty minimal clique separator $R$ of $G$ with $|R|<r$ lies inside one current block. Then for every small cut $S$ with $\delta_J(S)\ne\emptyset$ there are a current block $B$ and a component $C$ of $G-B$ with
--   $$\emptyset\ne\delta_J(C)\subseteq\delta_J(S).$$
--
--   Deleting each current block in turn and querying the components therefore exposes part of every surviving small-cut boundary.
--
--   Differences from the source:
--   - reading: "small-minimal-separator contractions are saturated" → every nonempty minimal clique separator R of G with |R| < r lies in one current block; reason: p.14: "When this phase stops, every small minimal clique separator lies in a single current block"
--   - encoding: "an enumerable current block B" → the block of some vertex u; reason: the current blocks are the ones enumerated
--   - reading: cache records, edge labels and available complete lists (Proposition 4.1) → the true residual quantities avail, knownMembers, envelope, numPoints; reason: the arguments are deterministic on the cache success event (p.9), where every value read is the true one and labels are injective on T_K (paper.md decision 7)
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 6.3, p.15 (PDF p.16); saturation of contractions, p.14

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_Safe
import Definitions.Def_HypRecov_envelope
import Definitions.Def_HypRecov_IsCompOf

namespace HypRecov

/-- **Lemma 6.3 (Cuts exposed by deleting a block).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 6.3, p.15
(PDF p.16): "Suppose completion and small-minimal-separator contractions are saturated. For any
original small cut S with nonempty residual boundary F, some component of G − B, for an enumerable
current block B, has a nonempty residual boundary contained in F." Saturation of the contractions,
p.14: "When this phase stops, every small minimal clique separator lies in a single current block."

Setting as in Lemma 6.1. Hypotheses: completion-terminal, and every nonempty minimal clique separator
`R` of `G` with `|R| < r` lies in one current block. Conclusion: for every `S` with `cut_H(S) < k` and
`δ_J(S) ≠ ∅` there are a current block `B` (the block of some vertex `u`) and a component `C` of
`G − B` with `∅ ≠ δ_J(C) ⊆ δ_J(S)`. -/
theorem lemma_6_3 {n : ℕ} (E D : Finset (Finset (Fin n))) (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (hE : ∀ e ∈ E, e.card = r) (hD : D ⊆ E) (P₀ P : Fin n → Fin n) (hco : Coarsens P₀ P)
    (hP : Safe E k P) (hterm : CompletionTerminal r (E \ D) P₀ P (Mpow k))
    (hsat : ∀ R : Finset (Fin n), R.Nonempty → R.card < r →
      IsMinCliqueSep (blockGraph (E \ D) P) R → ∃ b : Fin n, ∀ v ∈ R, P v = b)
    (S : Finset (Fin n)) (hS : cut E S < k) (hF : (bdry (E \ D) S).Nonempty) :
    ∃ (u : Fin n) (C : Finset (Fin n)),
      IsCompOf (blockGraph (E \ D) P) (Finset.univ.filter (fun v => P v = P u)) C ∧
        (bdry (E \ D) C).Nonempty ∧ bdry (E \ D) C ⊆ bdry (E \ D) S := by sorry

end HypRecov
