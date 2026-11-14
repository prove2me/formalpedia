-- Prove2me | Theorems.Thm_Lusztig_HeckeUnequal_prop_1_7
-- name    : Lusztig.HeckeUnequal.prop_1_7
-- status  : Proved
-- author  : @lookeng
-- created : 2026-11-13T18:08:12.709109+00:00
-- url     : https://prove2.me/theorems/889609ac-94d2-46c2-8acd-cae44446717d
-- title:
--   Lusztig, Hecke algebras with unequal parameters, Prop. 1.7 (exchange)
-- statement:
--   Let $(W,S)$ be a Coxeter system with length function $l$. Let $w \in W$ and $s \in S$ be such that $l(sw) = l(w) - 1$, and let $w = s_1 s_2 \cdots s_q$ be a reduced expression. Then there exists $j \in [1, q]$ such that
--   $$s\, s_1 s_2 \cdots s_{j-1} = s_1 s_2 \cdots s_j.$$
--   In the Lean statement the reduced expression is a list `ω` of indices with `cs.IsReduced ω` and `w = cs.wordProd ω`; the index $j$ of the source corresponds to `j + 1` (Lean lists are 0-indexed), so the conclusion reads `s * π(ω.take j) = π(ω.take (j+1))` with `j < ω.length`. The hypothesis $l(sw)=l(w)-1$ is written with natural-number subtraction, which is harmless since $l(sw) \neq l(w)$ always.
-- source:
--   G. Lusztig, Hecke algebras with unequal parameters, CRM Monograph Series 18 (AMS, 2003); arXiv:math/0208154v2 (2014), https://arxiv.org/abs/math/0208154, Chapter 1 (Coxeter groups), Proposition 1.7

import Mathlib.GroupTheory.Coxeter.Inversion

namespace Lusztig.HeckeUnequal

theorem prop_1_7 {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (w : W) (s : B) (hs : cs.length (cs.simple s * w) = cs.length w - 1)
    (ω : List B) (hω : cs.IsReduced ω) (hw : w = cs.wordProd ω) :
    ∃ j : ℕ, j < ω.length ∧
      cs.simple s * cs.wordProd (ω.take j) = cs.wordProd (ω.take (j + 1)) := by sorry

end Lusztig.HeckeUnequal
