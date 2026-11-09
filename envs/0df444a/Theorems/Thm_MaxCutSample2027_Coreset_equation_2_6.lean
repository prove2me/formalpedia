-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_equation_2_6
-- name    : MaxCutSample2027.Coreset.equation_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:51:16.641348+00:00
-- url     : https://prove2.me/theorems/da57b9a8-417e-4447-9046-eaeefdd1f67b
-- title:
--   §2.3, eq. (2.6) — closed form of the linear maximum
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For every nonnegative vector $q\in\mathbb R^V$ and every $c\in\mathbb R^V$, the defining linear maximum has the closed form
--   $$M_q(c):=\max_{a\in Z(q)}a^\top Kc=\sum_vq_v\max\{(Kc)_v,0\},\qquad (Kc)_v=\sum_uK_{vu}c_u.$$
--   This identifies the value of an independently defined optimization problem. The vector $q$ need not sum to one.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: the maximum over a nonnegative box → the real supremum of the bilinear image of Z(q); reason: the box is nonempty compact and the objective is continuous, so this is the same maximum
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), §2.3, eq. (2.6), p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem equation_2_6 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (q c : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    M (K A p) q c = ∑ v, q v * max ((∑ u, K A p v u * c u)) 0 := by sorry

end MaxCutSample2027.Coreset
