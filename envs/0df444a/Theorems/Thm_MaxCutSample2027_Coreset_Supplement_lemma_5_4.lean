-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_5_4
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:06:31.358305+00:00
-- url     : https://prove2.me/theorems/39804013-1dc7-4265-9c9f-a920e5865016
-- title:
--   Lemma 5.4 — the two r-way Max-Cut values
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$.
--
--   Fix an integer $r\ge2$. An r-way fractional cut belongs to $Z_r(q)=\{a:a^j_v\ge0,\sum_ja^j_v=q_v\}$, and $F_{K,r}(q)=\max_{a\in Z_r(q)}\sum_{j<\ell}(a^j)^\top Ka^\ell$. Write $T_K(a,c)=\sum_{j\ne\ell}(a^j)^\top Kc^\ell$, $M_{q,r}(c)=\max_{a\in Z_r(q)}T_K(a,c)$, $C_r(q,s)=\operatorname{conv}(Z_r(q)\cup-Z_r(q)\cup Z_r(s)\cup-Z_r(s))$, and $\Delta_{K,r}(q,s)=\max_{c\in C_r(q,s)}|M_{q,r}(c)-M_{s,r}(c)|$. For every $k\ge1$ and every sample outcome $x$,
--   $$F_{K,r}(p)=\frac{\operatorname{MaxCut}_r(A)}{n^2},\qquad F_{K,r}(P_x)=\frac{\operatorname{MaxCut}_r(\widehat A(x))}{n^2}.$$
--   Here $\operatorname{MaxCut}_r$ optimizes over all assignments of vertices to $r$ labels, allowing empty parts. The sample optimum is over assignments of all $k$ positions, with no requirement to keep repeated copies together. These two identities connect the fractional comparison model to the actual graph optima.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: the k sampled vertices and their empirical frequencies → Fin k sample positions and finite empirical counts; reason: all sample positions, including repeated draws, are retained in the two deterministic identities
--   - encoding: maxima over the fractional regions → real sSup of the same objective images; reason: the nonnegative-mass domains make the feasible sets nonempty and compact, so the continuous objectives attain their suprema
--   - encoding: r-way cut values of a symmetric matrix → the published Max3CutHard cut maximum applied to the matrix edge-list adapter, with vertex types in Type; reason: each ordered pair carries half its matrix weight, giving exactly the sum over j < l by symmetry; Type represents every finite source vertex set
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 5.4, p. 26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rFractional
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_5_4 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : 2 ≤ r)
    (x : Fin k → V) :
    FKr r (K A p) p = maxCutR r A / (Fintype.card V : ℝ) ^ 2 ∧
    FKr r (K A p) (empirical x) = maxCutR r (Ahat A p x) / (Fintype.card V : ℝ) ^ 2 := by sorry

end MaxCutSample2027.Coreset.Supplement
