-- Prove2me | Theorems.Thm_HiddenPartition_lemma_3_4
-- name    : HiddenPartition.lemma_3_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:28:30.002976+00:00
-- url     : https://prove2.me/theorems/933466b5-1080-4b32-916a-564b3ec1125b
-- title:
--   Lemma 3.4: the sets $C_a=\phi_a(S)$ partition $V(Z)$ into induced copies of $G[S]$
-- statement:
--   Throughout, $G$ is a finite simple graph whose vertex set is partitioned into $k$ non-empty independent domains $V(G)=V_1\sqcup\cdots\sqcup V_k$, $A$ and $B$ are finite non-empty sets with $|A|=|B|=M$, and $\mathcal F=\{f_v:A\to B\}_{v\in V(G)}$ is a family of maps with copy maps $\phi_a(v)=(\mathrm{dom}(v),f_v(a))$, images $W_a=\phi_a(V(G))$ and target graph $Z$ on $[k]\times B$ (Section 3.1).
--
--   Let $t\ge2$, let $\mathcal F$ be $t$-locally coherent, and let $S=\{\sigma_1,\dots,\sigma_k\}$ be a set of source vertices with $\sigma_i\in V_i$. Then the sets
--
--   $$C_a=\phi_a(S)=\{(i,f_{\sigma_i}(a)):i\in[k]\},\qquad a\in A,$$
--
--   partition the vertex set of $Z$ into $M=N/k$ parts, and each $C_a$ induces a copy of $G[S]$ via $\sigma_i\mapsto\phi_a(\sigma_i)$.
--
--   This is the covering guarantee of the construction, and it holds simultaneously for every choice of one vertex per domain.
--
--   **Formalization Note** $S$ is a map $[k]\to V(G)$ with $\mathrm{dom}(\sigma_i)=i$. "The $C_a$ partition $V(Z)$" is the bijectivity of $(a,i)\mapsto\phi_a(\sigma_i)$ from $A\times[k]$ onto $[k]\times B$; "induces a copy" is that $\phi_a(\sigma_i)\sim_Z\phi_a(\sigma_{i'})$ iff $\sigma_i\sim_G\sigma_{i'}$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §3.1 (domain partition of G; A, B finite nonempty with |A| = |B| = M) → binders IsDomainPartition G dom, [Fintype A] [Nonempty A] [Fintype B], Fintype.card A = Fintype.card B; reason: the section's standing assumptions written as hypotheses; same instances
--   - encoding: domains 1, …, k and vertex set [k] × B of Z → domains Fin k = {0, …, k−1}, vertex type Fin k × B, family f : V → A → B; reason: Lean indexing convention; same instances
--   - encoding: {C_a} partitions V(Z) into M = N/k parts, each inducing a copy of G[S] → (a, i) ↦ ϕ_a(σ_i) is a bijection A × Fin k → Fin k × B, and ϕ_a(σ_i) ~ ϕ_a(σ_i') ↔ σ_i ~ σ_i'; reason: a bijection from A × [k] is a partition into |A| = M parts of k vertices; the adjacency iff on the parts is the induced isomorphism; same instances
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Lemma 3.4, p.15 (pdf p.17)

import Mathlib
import Definitions.Def_HiddenPartition_IsDomainPartition
import Definitions.Def_HiddenPartition_IsLocallyCoherent

set_option autoImplicit false

namespace HiddenPartition

/-- **Lemma 3.4** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos, Zhang,
*From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering*, STOC 2027
submission (manuscript sha256 17239d0b…), p.15 (pdf p.17)).

For `t ≥ 2`, let `S = {σ_1, …, σ_k}` be a set of source vertices with `σ_i ∈ V_i`. Then the
collection of subsets `{C_a = ϕ_a(S)}_{a ∈ A}` partitions the vertex set of `Z` into
`M = N/k` parts, each of which induces a copy of `G[S]`.

**Formalization Note.** The standing assumptions of §3.1 (p.12) are binders: `G` is a
simple graph on a finite vertex type with a partition into `k` non-empty independent domains
(`IsDomainPartition`), `A` and `B` are finite non-empty sets with `|A| = |B|`, and
`f v = f_v`. `Z` is `target G dom f`, with vertex set `Fin k × B`.
`S` is a map `Fin k → V` with `dom (S i) = i`. "The `C_a` partition `V(Z)`" is the
bijectivity of `(a, i) ↦ ϕ_a(σ_i)` from `A × [k]` onto `[k] × B` (so there are `|A| = M`
parts of `k` vertices each); "`C_a` induces a copy of `G[S]`" is that `σ_i ↦ ϕ_a(σ_i)`
preserves adjacency and non-adjacency. -/
theorem lemma_3_4 {V A B : Type} [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k)
    (hdom : IsDomainPartition G dom) (hAB : Fintype.card A = Fintype.card B)
    (f : V → A → B) (t : ℕ) (ht : 2 ≤ t)
    (hf : IsLocallyCoherent t G dom f) (S : Fin k → V) (hS : ∀ i, dom (S i) = i) :
    Function.Bijective (fun p : A × Fin k => phi dom f p.1 (S p.2)) ∧
    ∀ a i i', (target G dom f).Adj (phi dom f a (S i)) (phi dom f a (S i')) ↔
      G.Adj (S i) (S i') := by sorry

end HiddenPartition
