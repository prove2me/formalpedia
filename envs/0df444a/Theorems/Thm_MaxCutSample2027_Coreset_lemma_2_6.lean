-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_6
-- name    : MaxCutSample2027.Coreset.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:48.315682+00:00
-- url     : https://prove2.me/theorems/33841ed5-1c80-407a-a1a7-e774fe723939
-- title:
--   Lemma 2.6 — matching fractional cuts
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For a nonnegative vector $q$, set $M_q(c)=\max_{a\in Z(q)}a^\top Kc$. For probability vectors $r,s$ (nonnegative coordinates summing to one), set $\mathcal C(r,s)=\operatorname{conv}(Z(r)\cup(-Z(r))\cup Z(s)\cup(-Z(s)))$ and $\Delta_K(r,s)=\max_{c\in\mathcal C(r,s)}|M_r(c)-M_s(c)|$.
--
--   For every pair of probability vectors $r,s$, both assertions hold:
--   $$\forall a\in Z(r),\ \exists b\in Z(s),\quad \max_{c\in\mathcal C(r,s)}|(a-b)^\top Kc|\le\Delta_K(r,s),$$
--   $$\max_{c\in\mathcal C(r,s)}|(r-s)^\top Kc|\le2\Delta_K(r,s).$$
--   The first bound chooses one $b$ that works for every $c$ simultaneously. The second is a separate conclusion; zero coordinates of $r,s$ are allowed.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: maxima over fractional boxes and their symmetric convex hull → compact-image real suprema on the same sets; reason: all domains are nonempty compact and all objectives are continuous, including M as a function of c
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.6, equations (2.10)–(2.11), p. 10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem lemma_2_6 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r s : V → ℝ) (hr : IsProbabilityVector r) (hs : IsProbabilityVector s) :
    (∀ a ∈ Z r, ∃ b ∈ Z s,
      maxAbsLinear (K A p) (a - b) (Ccal r s) ≤ DeltaK (K A p) r s) ∧
    maxAbsLinear (K A p) (r - s) (Ccal r s) ≤ 2 * DeltaK (K A p) r s := by sorry

end MaxCutSample2027.Coreset
