-- Prove2me | Theorems.Thm_HiddenPartition_lemma_3_1
-- name    : HiddenPartition.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:25.398656+00:00
-- url     : https://prove2.me/theorems/5f02c886-24ee-4068-ac9f-8dc2a6870ecd
-- title:
--   Lemma 3.1: perfect matchings of an $n$-regular bipartite graph of girth $\ge2(t+1)$ form a $t$-locally coherent family
-- statement:
--   Throughout, $G$ is a finite simple graph whose vertex set is partitioned into $k$ non-empty independent domains $V(G)=V_1\sqcup\cdots\sqcup V_k$, $A$ and $B$ are finite non-empty sets with $|A|=|B|=M$, and $\mathcal F=\{f_v:A\to B\}_{v\in V(G)}$ is a family of maps with copy maps $\phi_a(v)=(\mathrm{dom}(v),f_v(a))$, images $W_a=\phi_a(V(G))$ and target graph $Z$ on $[k]\times B$ (Section 3.1).
--
--   For $t\ge1$, let $J$ be a simple $n$-regular bipartite graph with bipartition $(A,B)$ and girth at least $2(t+1)$, where $n=|V(G)|$. Fix a decomposition $E(J)=\bigsqcup_{v\in V(G)}M_v$ into perfect matchings, and define $f_v(a)=b$ if and only if $(a,b)\in M_v$. Then
--
--   $$\mathcal F=\{f_v:A\to B\}_{v\in V(G)}\ \text{is a $t$-locally coherent family with respect to the domain partition of } G.$$
--
--   This is how the construction obtains its family of bijections: from a high-girth regular bipartite graph (Lemma 3.2) and its decomposition into perfect matchings.
--
--   **Formalization Note** $J$ is a simple graph on $A\sqcup B$ with no edge inside a side. The decomposition is given through the maps themselves: every $f_v$ is a bijection ($M_v$ is a perfect matching), $a\sim_J b$ iff $f_v(a)=b$ for some $v$ (the $M_v$ cover $E(J)$), and $f_v(a)=f_w(a)$ implies $v=w$ (the $M_v$ are disjoint). The printed hypothesis "$n$-regular" is kept although it follows from these.
--
--   Differences from the source:
--   - encoding: standing assumptions of §3.1 (domain partition of G; A, B finite nonempty with |A| = |B| = M) → binders IsDomainPartition G dom, [Fintype A] [Nonempty A] [Fintype B], Fintype.card A = Fintype.card B; reason: the section's standing assumptions written as hypotheses; same instances
--   - encoding: domains 1, …, k and vertex set [k] × B of Z → domains Fin k = {0, …, k−1}, vertex type Fin k × B, family f : V → A → B; reason: Lean indexing convention; same instances
--   - encoding: a decomposition E(J) = ⊔_v M_v into perfect matchings with f_v(a) = b iff (a, b) ∈ M_v → f : V → A → B with each f v bijective, J.Adj (inl a) (inr b) ↔ ∃ v, f v a = b, and f v a = f w a → v = w; reason: M_v is the graph of f_v; perfect ⇔ bijective, cover ⇔ the iff, disjoint ⇔ the injectivity in v; same instances
--   - encoding: girth (infinite for a forest) → Mathlib extended girth egirth : ℕ∞; reason: same value; ⊤ for a forest as on p.9
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Lemma 3.1, p.13 (pdf p.15)

import Mathlib
import Definitions.Def_HiddenPartition_IsDomainPartition
import Definitions.Def_HiddenPartition_IsLocallyCoherent

set_option autoImplicit false

open Classical

namespace HiddenPartition

/-- **Lemma 3.1** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos, Zhang,
*From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering*, STOC 2027
submission (manuscript sha256 17239d0b…), p.13 (pdf p.15)).

Let `G` be a graph on `n` vertices partitioned into `k` independent domains. For `t ≥ 1`, let
`J` be a simple `n`-regular bipartite graph with bipartition `(A, B)` and girth at least
`2(t + 1)`. Fix a decomposition `E(J) = ⨆_{v ∈ V(G)} M_v` into perfect matchings and define
`f_v(a) = b` iff `(a, b) ∈ M_v`. Then `F = {f_v : A → B}_{v ∈ V(G)}` is a `t`-locally coherent
family with respect to the domain partition of `G`.

**Formalization Note.**
* `J : SimpleGraph (A ⊕ B)` with no edge inside `A` or inside `B`; `n`-regular is
  `J.IsRegularOfDegree (Fintype.card V)`; girth is `egirth`.
* The decomposition is given through the family `f` itself: every `f v` is a bijection
  (`M_v` is a perfect matching), `inl a ~ inr b` in `J` iff `f v a = b` for some `v`
  (the `M_v` cover `E(J)`), and `f v a = f w a → v = w` (the `M_v` are disjoint).
* `A` is non-empty (§3.1: "`A` and `B` finite nonempty sets"); the domain partition is the
  standing assumption of §3.1. -/
theorem lemma_3_1 {V A B : Type} [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k)
    (hdom : IsDomainPartition G dom) (t : ℕ) (ht : 1 ≤ t)
    (J : SimpleGraph (A ⊕ B))
    (hJA : ∀ a a' : A, ¬ J.Adj (Sum.inl a) (Sum.inl a'))
    (hJB : ∀ b b' : B, ¬ J.Adj (Sum.inr b) (Sum.inr b'))
    (hJreg : J.IsRegularOfDegree (Fintype.card V))
    (hJgirth : ((2 * (t + 1) : ℕ) : ℕ∞) ≤ J.egirth)
    (f : V → A → B) (hfbij : ∀ v, Function.Bijective (f v))
    (hfcover : ∀ a b, J.Adj (Sum.inl a) (Sum.inr b) ↔ ∃ v, f v a = b)
    (hfdisj : ∀ v w a, f v a = f w a → v = w) :
    IsLocallyCoherent t G dom f := by sorry

end HiddenPartition
