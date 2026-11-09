-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_5
-- name    : MaxCutSample2027.Coreset.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:46.276777+00:00
-- url     : https://prove2.me/theorems/8992ae60-9b8c-428f-87f9-ca06ae061e3d
-- title:
--   Lemma 2.5 — comparison of cut values
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For a nonnegative vector $q$, set $M_q(c)=\max_{a\in Z(q)}a^\top Kc$. For probability vectors $r,s$ (nonnegative coordinates summing to one), set $\mathcal C(r,s)=\operatorname{conv}(Z(r)\cup(-Z(r))\cup Z(s)\cup(-Z(s)))$ and $\Delta_K(r,s)=\max_{c\in\mathcal C(r,s)}|M_r(c)-M_s(c)|$.
--
--   For every pair of probability vectors $r,s$,
--   $$|F_K(r)-F_K(s)|\le4\Delta_K(r,s).$$
--   This compares the full fractional optimum under two distributions, including distributions with zero coordinates.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: fractional and comparison maxima → compact-image real suprema on the same sets; reason: all domains are nonempty compact and the displayed objectives attain their maxima
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.5, equation (2.9), p. 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem lemma_2_5 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r s : V → ℝ) (hr : IsProbabilityVector r) (hs : IsProbabilityVector s) :
    |FK (K A p) r - FK (K A p) s| ≤ 4 * DeltaK (K A p) r s := by sorry

end MaxCutSample2027.Coreset
