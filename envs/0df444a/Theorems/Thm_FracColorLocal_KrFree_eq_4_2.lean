-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_eq_4_2
-- name    : FracColorLocal.KrFree.eq_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:32.510205+00:00
-- url     : https://prove2.me/theorems/007f53c9-e518-4450-83d8-efa3911e3caa
-- title:
--   (4.2) — the potential is at most Φ: U_{G,u}(w) ≤ Φ_{G,u}(w) for every positive w
-- statement:
--   Let $G$ be any finite graph (isolated vertices allowed) and $u>0$ an objective weight. For every positive vertex weight $w$,
--
--   $$U_{G,u}(w)\ \le\ \Phi_{G,u}(w),$$
--
--   where $U_{G,u}(w)=\sum_vU_{u(v)}(w(v))-2M_G(w)$ and $\Phi_{G,u}(w)=\sum_vu(v)f(d_{G,w}(v))$.
--
--   Together with Lemma 4.1 this shows that $U$ and $\Phi$ have the same supremum, and it is used on the graphs $G_x$ in the induction of §6.
--
--   Differences from the source: none.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 17 (PDF 18), §4.1, (4.2) (standing assumption u > 0 of §4, p. 16)

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Potential

namespace FracColorLocal.KrFree

/-- (4.2): `U_{G,u}(w) ≤ Φ_{G,u}(w)` for every positive `w`, on every graph. -/
theorem eq_4_2 {V : Type*} [Fintype V] (G : SimpleGraph V) (u w : V → ℝ)
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) :
    potential G u w ≤ phiPot G u w := by sorry

end FracColorLocal.KrFree
