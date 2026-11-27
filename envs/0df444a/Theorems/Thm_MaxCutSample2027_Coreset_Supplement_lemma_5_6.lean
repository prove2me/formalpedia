-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_5_6
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_5_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T10:06:59.467361+00:00
-- url     : https://prove2.me/theorems/b76badcb-02d6-44f0-926c-c143f8fbe39b
-- title:
--   Lemma 5.6 — matching fractional r-way cuts in both directions
-- statement:
--   Let $V$ be a finite nonempty set of size $n$, let $A$ be a symmetric nonnegative real matrix with zero diagonal, and let $p$ be a positive probability vector. Write $K_{uv}=A_{uv}/(n^2p_up_v)$ and $H=\sum_vp_v\sqrt{\sum_up_uK_{uv}^2}$. Sample positions are independent draws from $p$ with replacement; their empirical law is $P_X$, and the sampled graph on $[k]$ has weights $\widehat A_{ij}=A_{X_iX_j}/(k^2p_{X_i}p_{X_j})$.
--
--   Fix an integer $r\ge2$. An r-way fractional cut belongs to $Z_r(q)=\{a:a^j_v\ge0,\sum_ja^j_v=q_v\}$, and $F_{K,r}(q)=\max_{a\in Z_r(q)}\sum_{j<\ell}(a^j)^\top Ka^\ell$. Write $T_K(a,c)=\sum_{j\ne\ell}(a^j)^\top Kc^\ell$, $M_{q,r}(c)=\max_{a\in Z_r(q)}T_K(a,c)$, $C_r(q,s)=\operatorname{conv}(Z_r(q)\cup-Z_r(q)\cup Z_r(s)\cup-Z_r(s))$, and $\Delta_{K,r}(q,s)=\max_{c\in C_r(q,s)}|M_{q,r}(c)-M_{s,r}(c)|$. Let $q,s$ be any probability vectors, allowing zero coordinates. Both directions hold:
--   $$\forall a\in Z_r(q),\ \exists b\in Z_r(s),\quad\max_{c\in C_r(q,s)}|T_K(a-b,c)|\le\Delta_{K,r}(q,s),$$
--   $$\forall b\in Z_r(s),\ \exists a\in Z_r(q),\quad\max_{c\in C_r(q,s)}|T_K(a-b,c)|\le\Delta_{K,r}(q,s).$$
--   Each matching works simultaneously for every $c$ in the same convex symmetric region. This is the r-way matching result used by the comparison inequality.
--
--   Differences from the source:
--   - generalization: discard isolated vertices and assume d(v) > 0 in the standing setup → all symmetric nonnegative zero-diagonal matrices, including isolated vertices; reason: isolated vertices contribute zero; restricting to graphs with positive degrees recovers every source instance
--   - encoding: r parts of vectors indexed by V → Fin r and finite function types; reason: index relabeling represents the same fractional cuts and finite sums
--   - encoding: maxima over the fractional regions → real sSup of the same objective images; reason: the nonnegative-mass domains make the feasible sets nonempty and compact, so the continuous objectives attain their suprema
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 5.6, p. 27. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rFractional
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_5_6 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r : ℕ) (hr : 2 ≤ r)
    (q s : V → ℝ) (hq : IsProbabilityVector q) (hs : IsProbabilityVector s)
    : (∀ a ∈ Zr r q, ∃ b ∈ Zr r s,
        matchingErrorR (K A p) a b (Cr r q s) ≤ DeltaKr r (K A p) q s) ∧
      (∀ b ∈ Zr r s, ∃ a ∈ Zr r q,
        matchingErrorR (K A p) a b (Cr r q s) ≤ DeltaKr r (K A p) q s) := by sorry

end MaxCutSample2027.Coreset.Supplement
