-- Prove2me | Theorems.Thm_HiddenPartition_lemma_4_1
-- name    : HiddenPartition.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:53.311146+00:00
-- url     : https://prove2.me/theorems/0e2820a3-eb23-4d2d-8d08-0b874be92365
-- title:
--   Lemma 4.1: $\mathrm{ED}_Z(X)\le\min\{(s-1)/2,\,(s(B_G(s)+s)/4)^{1/3}\}$ for 4-locally coherent families
-- statement:
--   Throughout, $G$ is a finite simple graph whose vertex set is partitioned into $k$ non-empty independent domains $V(G)=V_1\sqcup\cdots\sqcup V_k$, $A$ and $B$ are finite non-empty sets with $|A|=|B|=M$, and $\mathcal F=\{f_v:A\to B\}_{v\in V(G)}$ is a family of maps with copy maps $\phi_a(v)=(\mathrm{dom}(v),f_v(a))$, images $W_a=\phi_a(V(G))$ and target graph $Z$ on $[k]\times B$ (Section 3.1).
--
--   Let $\mathcal F$ be $4$-locally coherent (in the paper, $Z$ is built as in Section 3 with $t=4$, from the girth-10 graph of Lemma 3.2). For every $X\subseteq V(Z)$ of size $s\ge1$,
--
--   $$\mathrm{ED}_Z(X)=\frac{|E(Z[X])|}{s}\le\min\left\{\frac{s-1}{2},\ \left(\frac{s\,(B_G(s)+s)}{4}\right)^{1/3}\right\},\qquad B_G(s)=\max_{S\subseteq V(G),\ |S|\le s}|E(G[S])|.$$
--
--   This density bound transfers the absence of dense small subgraphs from $G$ to $Z$ and drives the hardness results for Densest-$q$-Partition and Min-Sum Clustering.
--
--   **Formalization Note** The inequality is in $\mathbb R$; the cube root is the real power with exponent $1/3$ of a non-negative number.
--
--   Differences from the source:
--   - generalization: Z constructed as in Section 3 with t = 4 from Lemma 3.2's girth-10 graph via Lemma 3.1 → Z = target G dom f for every 4-locally coherent family f; reason: the paper's family is 4-locally coherent (Lemma 3.1), so the Lean statement specializes to it; the proof uses only 4-coherence and Lemma 3.3
--   - encoding: standing assumptions of §3.1 (domain partition of G; A, B finite nonempty with |A| = |B| = M) → binders IsDomainPartition G dom, [Fintype A] [Nonempty A] [Fintype B], Fintype.card A = Fintype.card B; reason: the section's standing assumptions written as hypotheses; same instances
--   - encoding: domains 1, …, k and vertex set [k] × B of Z → domains Fin k = {0, …, k−1}, vertex type Fin k × B, family f : V → A → B; reason: Lean indexing convention; same instances
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Lemma 4.1, p.17 (pdf p.19), with the construction of §4, p.17

import Mathlib
import Definitions.Def_HiddenPartition_IsDomainPartition
import Definitions.Def_HiddenPartition_IsLocallyCoherent
import Definitions.Def_HiddenPartition_edgeCount
import Definitions.Def_HiddenPartition_bMax

set_option autoImplicit false

namespace HiddenPartition

/-- **Lemma 4.1** (Agrawal, Eua-anant, Haeupler, Laekhanukit, Mihov, Milenković, Santos, Zhang,
*From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering*, STOC 2027
submission (manuscript sha256 17239d0b…), p.17 (pdf p.19)).

Let `Z` be constructed as in Section 3 with `t = 4`. For any `X ⊆ V(Z)` of size `s ≥ 1`,
`ED_Z(X) ≤ min{(s - 1)/2, (s · (B_G(s) + s)/4)^{1/3}}`, where
`B_G(s) = max_{S ⊆ V(G), |S| ≤ s} |E(G[S])|` and `ED_Z(X) = |E(Z[X])| / |X|`.

**Formalization Note.** The standing assumptions of §3.1 (p.12) are binders: `G` is a
simple graph on a finite vertex type with a partition into `k` non-empty independent domains
(`IsDomainPartition`), `A` and `B` are finite non-empty sets with `|A| = |B|`, and
`f v = f_v`. `Z` is `target G dom f`, with vertex set `Fin k × B`.
The paper's `Z` comes from Lemma 3.2's girth-10 graph through Lemma 3.1; here `F` is any
`4`-locally coherent family (a generalization: the paper's family is one of them). The
inequality is in `ℝ`; `(·)^{1/3}` is `Real.rpow` with exponent `(1/3 : ℝ)` of a non-negative
base. -/
theorem lemma_4_1 {V A B : Type} [Fintype V] [DecidableEq V] [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] {k : ℕ} (G : SimpleGraph V) (dom : V → Fin k)
    (hdom : IsDomainPartition G dom) (hAB : Fintype.card A = Fintype.card B)
    (f : V → A → B)
    (hf : IsLocallyCoherent 4 G dom f) (X : Finset (Fin k × B)) (hX : 1 ≤ X.card) :
    (edgeCount (target G dom f) X : ℝ) / X.card ≤
      min (((X.card : ℝ) - 1) / 2)
        (((X.card : ℝ) * ((bMax G X.card : ℝ) + X.card) / 4) ^ (1 / 3 : ℝ)) := by sorry

end HiddenPartition
