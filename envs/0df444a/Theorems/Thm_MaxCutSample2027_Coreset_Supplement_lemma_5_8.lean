-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_5_8
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_5_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T10:10:22.897209+00:00
-- url     : https://prove2.me/theorems/1e84e643-7fda-472c-822b-981f6b8e54b0
-- title:
--   Lemma 5.8 — bound for the r-way signed maximum
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$.
--
--   Fix an integer $r\ge2$. An r-way fractional cut belongs to $Z_r(q)=\{a:a^j_v\ge0,\sum_ja^j_v=q_v\}$, and $F_{K,r}(q)=\max_{a\in Z_r(q)}\sum_{j<\ell}(a^j)^\top Ka^\ell$. Write $T_K(a,c)=\sum_{j\ne\ell}(a^j)^\top Kc^\ell$, $M_{q,r}(c)=\max_{a\in Z_r(q)}T_K(a,c)$, $C_r(q,s)=\operatorname{conv}(Z_r(q)\cup-Z_r(q)\cup Z_r(s)\cup-Z_r(s))$, and $\Delta_{K,r}(q,s)=\max_{c\in C_r(q,s)}|M_{q,r}(c)-M_{s,r}(c)|$.
--
--   For independent samples $X,Y$ of size $k\ge1$ and independent uniform signs $\sigma_{ij}$ ($0\le j\le r$), write $B^{(r)}_{X,Y}=\{c:\sum_j|c^j_v|\le p_v+P_X(v)+P_Y(v)\ \forall v\}$ and $R=\max_{c\in B^{(r)}_{X,Y}}|k^{-1}\sum_i\sum_{j=1}^r(\sigma_{i0}+\sigma_{ij})(Kc^j)_{X_i}|$. Then
--   $$\mathbb E_{X,Y,\sigma}R\le6\sqrt2H\sqrt{\frac{\log(2r)}k}.$$
--   The logarithm is natural. No upper bound on the edge weights is imposed. This bounds exactly the signed maximum appearing in Lemma 5.7, with the same box and sign law.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: expectations over independent samples and uniform signs → nested finite product-law sums and uniform Boolean sign-matrix averages; reason: the nested sums give the exact independent laws of X, Y and all k(r+1) signs, with every sample position retained
--   - encoding: the maximum over the signed l1 box → real sSup of the continuous objective image of boxR; reason: the nonnegative radii make this finite-dimensional box nonempty and compact, so the supremum is attained
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 5.8, p. 31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rSigned
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_5_8 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : 2 ≤ r)
    : expectedSignedR r k (K A p) p ≤
      6 * Real.sqrt 2 * H A p * Real.sqrt (Real.log (2 * (r : ℝ)) / (k : ℝ)) := by sorry

end MaxCutSample2027.Coreset.Supplement
