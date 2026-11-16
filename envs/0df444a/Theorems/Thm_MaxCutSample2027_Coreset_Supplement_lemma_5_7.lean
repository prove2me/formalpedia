-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_5_7
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:09:13.599407+00:00
-- url     : https://prove2.me/theorems/aac6e318-a5ba-49b0-a65a-c8aeca4257ed
-- title:
--   Lemma 5.7 — reduction to a signed r-way maximum
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$.
--
--   Fix an integer $r\ge2$. An r-way fractional cut belongs to $Z_r(q)=\{a:a^j_v\ge0,\sum_ja^j_v=q_v\}$, and $F_{K,r}(q)=\max_{a\in Z_r(q)}\sum_{j<\ell}(a^j)^\top Ka^\ell$. Write $T_K(a,c)=\sum_{j\ne\ell}(a^j)^\top Kc^\ell$, $M_{q,r}(c)=\max_{a\in Z_r(q)}T_K(a,c)$, $C_r(q,s)=\operatorname{conv}(Z_r(q)\cup-Z_r(q)\cup Z_r(s)\cup-Z_r(s))$, and $\Delta_{K,r}(q,s)=\max_{c\in C_r(q,s)}|M_{q,r}(c)-M_{s,r}(c)|$.
--
--   For independent samples $X,Y$ of size $k\ge1$ and independent uniform signs $\sigma_{ij}$ ($0\le j\le r$), write $B^{(r)}_{X,Y}=\{c:\sum_j|c^j_v|\le p_v+P_X(v)+P_Y(v)\ \forall v\}$ and $R=\max_{c\in B^{(r)}_{X,Y}}|k^{-1}\sum_i\sum_{j=1}^r(\sigma_{i0}+\sigma_{ij})(Kc^j)_{X_i}|$. Then
--   $$\mathbb E_X\Delta_{K,r}(p,P_X)\le8\mathbb E_{X,Y,\sigma}R.$$
--   All $k(r+1)$ signs are independent, including the extra shared coordinate. The same l1 box and signed maximum are used in Lemma 5.8. This is the source's reduction to the signed quantity.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: expectations over independent samples and uniform signs → nested finite product-law sums and uniform Boolean sign-matrix averages; reason: the nested sums give the exact independent laws of X, Y and all k(r+1) signs, with every sample position retained
--   - encoding: maxima defining the fractional discrepancy and the signed l1-box objective → real sSup over the same feasible regions; reason: the probability simplexes, their symmetric convex hull and the nonnegative-radius signed box are nonempty compact sets; all objectives are continuous
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 5.7, p. 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rSigned
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_5_7 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : 2 ≤ r)
    : sampleAverage p k (fun x => DeltaKr r (K A p) p (empirical x)) ≤
      8 * expectedSignedR r k (K A p) p := by sorry

end MaxCutSample2027.Coreset.Supplement
