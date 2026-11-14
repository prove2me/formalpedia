-- Prove2me | Theorems.Thm_Lusztig_HeckeUnequal_prop_1_10
-- name    : Lusztig.HeckeUnequal.prop_1_10
-- status  : Proved
-- author  : @lookeng
-- created : 2026-11-13T18:08:11.478894+00:00
-- url     : https://prove2.me/theorems/ff48279e-ef78-433e-bdf7-a84d660c00fc
-- title:
--   Lusztig, Hecke algebras with unequal parameters, Prop. 1.10
-- statement:
--   Let $(W,S)$ be a Coxeter system with length function $l$. Let $w \in W$ and $s, t \in S$ be such that
--   $$l(swt) = l(w), \qquad l(sw) = l(wt).$$
--   Then $sw = wt$.
-- source:
--   G. Lusztig, Hecke algebras with unequal parameters, CRM Monograph Series 18 (AMS, 2003); arXiv:math/0208154v2 (2014), https://arxiv.org/abs/math/0208154, Chapter 1 (Coxeter groups), Proposition 1.10

import Mathlib.GroupTheory.Coxeter.Length

namespace Lusztig.HeckeUnequal

theorem prop_1_10 {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (w : W) (s t : B)
    (h₁ : cs.length (cs.simple s * w * cs.simple t) = cs.length w)
    (h₂ : cs.length (cs.simple s * w) = cs.length (w * cs.simple t)) :
    cs.simple s * w = w * cs.simple t := by sorry

end Lusztig.HeckeUnequal
