-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_3
-- name    : MaxCutSample2027.Coreset.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:12.277554+00:00
-- url     : https://prove2.me/theorems/7998deb4-5e77-4878-9abb-dd9459f99c34
-- title:
--   Lemma 2.3 — the maximum is attained by a cut
-- statement:
--   Let $V$ be a finite nonempty vertex set, $n=|V|$, and let $A:V\times V\to\mathbb R$ be symmetric with zero diagonal and nonnegative entries. Let $p$ satisfy $p_v>0$ for every vertex and $\sum_vp_v=1$. Define $K_{uv}=A_{uv}/(n^2p_up_v)$.
--
--   For a nonnegative vector $r$, write $Z(r)=\{a\in\mathbb R^V:0\le a_v\le r_v\text{ for every }v\}$ and $F_K(r)=\max_{a\in Z(r)}a^\top K(r-a)$, where $a^\top Kc=\sum_{u,v}a_uK_{uv}c_v$.
--
--   For every such $r$, there exists $a$ satisfying
--   $$a\in Z(r),\qquad a^\top K(r-a)=F_K(r),\qquad \forall v\in V,\ a_v\in\{0,r_v\}.$$
--   An ordinary cut therefore attains the fractional optimum, even when $r$ is not normalized to a probability vector.
--
--   **Formalization Note** Every real supremum here is an attained maximum of a continuous function on a nonempty compact domain. Any expectation is an explicit finite product-law sum.
--
--   Differences from the source:
--   - generalization: the standing assumption d(v)>0 for every vertex → isolated vertices are allowed; reason: no quantity or step of §2.2–§2.4 divides by a degree; imposing positive degrees recovers every source instance
--   - encoding: finite vertex sets and a fractional maximum → Fintype vertices and a compact-image real supremum; reason: the nonnegative box is nonempty compact and the continuous objective attains its supremum
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma 2.3, p. 8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7).

import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

namespace MaxCutSample2027.Coreset

theorem lemma_2_3 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r : V → ℝ) (hr : ∀ v, 0 ≤ r v) :
    ∃ a ∈ Z r, bilinear (K A p) a (r - a) = FK (K A p) r ∧
      ∀ v, a v = 0 ∨ a v = r v := by sorry

end MaxCutSample2027.Coreset
