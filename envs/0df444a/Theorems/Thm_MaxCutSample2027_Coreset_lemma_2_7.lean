-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_7
-- name    : MaxCutSample2027.Coreset.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:51:03.162136+00:00
-- url     : https://prove2.me/theorems/1581af16-d99c-4874-afef-f4fdef1469af
-- title:
--   Lemma 2.7 — reduction to a signed linear maximum
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For a nonnegative vector $q$, set $M_q(c)=\max_{a\in Z(q)}a^\top Kc$. For probability vectors $r,s$ (nonnegative coordinates summing to one), set $\mathcal C(r,s)=\operatorname{conv}(Z(r)\cup(-Z(r))\cup Z(s)\cup(-Z(s)))$ and $\Delta_K(r,s)=\max_{c\in\mathcal C(r,s)}|M_r(c)-M_s(c)|$.
--
--   For an integer $k\ge1$, let $X=(X_0,\ldots,X_{k-1})$ be independent draws with replacement from $p$, and let $P_X(v)=|\{i:X_i=v\}|/k$.
--
--   Let $Y$ be an independent sample with the same law and empirical distribution $P_Y$. Let $\sigma_0,\ldots,\sigma_{k-1}$ be independent uniform signs in $\{-1,1\}$, independent of both samples. Define
--   $$B_{X,Y}=\{c\in\mathbb R^V: |c_v|\le p_v+P_X(v)+P_Y(v)\text{ for every }v\},\qquad
--   S_K(X,Y,\sigma)=\max_{c\in B_{X,Y}}\left|\frac1k\sum_{i=0}^{k-1}\sigma_i(Kc)_{X_i}\right|,$$
--   where $(Kc)_u=\sum_vK_{uv}c_v$.
--
--   Then
--   $$\mathbb E_X\Delta_K(p,P_X)\le4\mathbb E_{X,Y,\sigma}S_K(X,Y,\sigma).$$
--   This bounds the comparison gap by the signed linear maximum on the specified sample-dependent box.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: independent samples and signs and maxima on C(p,P_X) and B(X,Y) → explicit finite product-law averages, Fin k positions, Boolean signs, and compact-image real suprema; reason: all outcomes and their probabilities are retained and every supremum is finite and attained
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.7, equation (2.15), p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_signed
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem lemma_2_7 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x => DeltaK (K A p) p (empirical x)) ≤
      4 * jointAverage p k (signedMaximum (K A p) p) := by sorry

end MaxCutSample2027.Coreset
