-- Prove2me | Theorems.Thm_HiddenPartition_lemma_3_5
-- name    : HiddenPartition.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:31.918716+00:00
-- url     : https://prove2.me/theorems/918fd923-3e1f-4f63-83fe-f95fbde51ff1
-- title:
--   Lemma 3.5: cliques of $Z$ lie in a unique induced copy, and $\omega(Z)=\omega(G)$
-- statement:
--   Throughout, $G$ is a finite simple graph whose vertex set is partitioned into $k$ non-empty independent domains $V(G)=V_1\sqcup\cdots\sqcup V_k$, $A$ and $B$ are finite non-empty sets with $|A|=|B|=M$, and $\mathcal F=\{f_v:A\to B\}_{v\in V(G)}$ is a family of maps with copy maps $\phi_a(v)=(\mathrm{dom}(v),f_v(a))$, images $W_a=\phi_a(V(G))$ and target graph $Z$ on $[k]\times B$ (Section 3.1).
--
--   Let $t\ge3$ and let $\mathcal F$ be $t$-locally coherent. Then every clique $Q$ of $Z$ with at least two vertices lies in a unique induced copy, i.e. $Q\subseteq W_a$ for exactly one seed $a$. Consequently
--
--   $$\omega(Z)=\omega(G),$$
--
--   where $\omega(F)$ is the size of a maximum clique of $F$.
--
--   This is the soundness half of the reduction from Clique to Coloring: the construction creates no new cliques.
--
--   **Formalization Note** $\omega$ is Mathlib's `cliqueNum` (the maximum clique size on a finite vertex type, $0$ for the empty graph).
--
--   Differences from the source:
--   - encoding: standing assumptions of §3.1 (domain partition of G; A, B finite nonempty with |A| = |B| = M) → binders IsDomainPartition G dom, [Fintype A] [Nonempty A] [Fintype B], Fintype.card A = Fintype.card B; reason: the section's standing assumptions written as hypotheses; same instances
--   - encoding: domains 1, …, k and vertex set [k] × B of Z → domains Fin k = {0, …, k−1}, vertex type Fin k × B, family f : V → A → B; reason: Lean indexing convention; same instances
--   - encoding: lies in a unique induced copy → ∃! a, Q ⊆ W_a; reason: the induced copies are the Z[W_a]; a set of ≥ 2 vertices inside two of them would violate single-vertex overlap, so unique copy and unique seed agree
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Lemma 3.5, p.16 (pdf p.18)

import Mathlib
import Definitions.Def_HiddenPartition_IsDomainPartition
import Definitions.Def_HiddenPartition_IsLocallyCoherent

set_option autoImplicit false

namespace HiddenPartition

/-- **Lemma 3.5** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos, Zhang,
*From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering*, STOC 2027
submission (manuscript sha256 17239d0b…), p.16 (pdf p.18)).

For `t ≥ 3`, every clique in `Z` with at least two vertices lies in a unique induced copy.
Consequently `ω(Z) = ω(G)`, where `ω(F)` denotes the size of a maximum clique in a graph `F`.

**Formalization Note.** The standing assumptions of §3.1 (p.12) are binders: `G` is a
simple graph on a finite vertex type with a partition into `k` non-empty independent domains
(`IsDomainPartition`), `A` and `B` are finite non-empty sets with `|A| = |B|`, and
`f v = f_v`. `Z` is `target G dom f`, with vertex set `Fin k × B`.
"Lies in a unique induced copy" is: there is exactly one seed `a` with `Q ⊆ W_a` (distinct
seeds give distinct copies `Z[W_a]`). `ω` is Mathlib's `cliqueNum` (a maximum on a finite
vertex type; `0` on the empty graph). -/
theorem lemma_3_5 {V A B : Type} [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k)
    (hdom : IsDomainPartition G dom) (hAB : Fintype.card A = Fintype.card B)
    (f : V → A → B) (t : ℕ) (ht : 3 ≤ t)
    (hf : IsLocallyCoherent t G dom f) :
    (∀ Q : Finset (Fin k × B), (target G dom f).IsClique (Q : Set (Fin k × B)) → 2 ≤ Q.card →
      ∃! a, Q ⊆ W dom f a) ∧
    (target G dom f).cliqueNum = G.cliqueNum := by sorry

end HiddenPartition
