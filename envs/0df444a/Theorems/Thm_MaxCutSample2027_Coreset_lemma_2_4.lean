-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_4
-- name    : MaxCutSample2027.Coreset.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:19.932182+00:00
-- url     : https://prove2.me/theorems/56460d39-d5ed-4555-aca6-fcbb61fc22c4
-- title:
--   Lemma 2.4 — the two Max-Cut values
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   Fix $k\ge1$ and any sample outcome $x:\operatorname{Fin}(k)\to V$. Set $P_x(v)=|\{i:x_i=v\}|/k$ and $\widehat A_{ij}(x)=A_{x_ix_j}/(k^2p_{x_i}p_{x_j})$. For a finite matrix $B$ on vertices $W$, let $\operatorname{MaxCut}(B)=\max_{S\subseteq W}\sum_{u\in S,v\notin S}B_{uv}$. Then
--   $$F_K(p)=\frac{\operatorname{MaxCut}(A)}{n^2},\qquad F_K(P_x)=\frac{\operatorname{MaxCut}(\widehat A(x))}{n^2}.$$
--   Both identities are asserted, and the sampled identity holds for every outcome. The sampled maximum permits all subsets of the sample positions, including subsets that separate copies of one original vertex.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: finite sets and sample positions indexed from 1 to k → Fintype vertices, Fin k sample positions, a finite cut maximum and compact-image real suprema; reason: reindexing retains every sample and every cut; all suprema here are attained
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.4, p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem lemma_2_4 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) (x : Fin k → V) :
    FK (K A p) p = maxCut A / (Fintype.card V : ℝ) ^ 2 ∧
    FK (K A p) (empirical x) = maxCut (Ahat A p x) / (Fintype.card V : ℝ) ^ 2 := by sorry

end MaxCutSample2027.Coreset
