-- Prove2me | Theorems.Thm_GeneralCK_finiteHybridBellman
-- name    : GeneralCK.finiteHybridBellman
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-24T22:32:51.122501+00:00
-- url     : https://prove2.me/theorems/158cfda9-c899-41a0-9fed-004f92d74e42
-- title:
--   Finite hybrid Bellman inequality for interior binary laws
-- statement:
--   Let $H$ be binary entropy in bits, let $B$ be the hybrid Bellman profile of the accompanying definition, let $J(x)=\log((1-x)/x)/\log 2$ for $0<x<1$, and let $c(u,v)=(v-u)(J(u)-J(v))/2$ be its interior edge cost. For any finite family of nonnegative weights $w_i$ summing to one and values $u_i,v_i\in(0,1)$, define
--
--   $$a=\sum_i w_i u_i,\qquad b=\sum_i w_i v_i,\qquad e=\sum_i w_i H(u_i),\qquad f=\sum_i w_i H(v_i).$$
--
--   The required inequality is
--
--   $$B\!\left(\frac{a+b}{2},\frac{e+f}{2}\right)\le \frac{B(a,e)+B(b,f)}{2}+\sum_i w_i c(u_i,v_i).$$
--
--   There is no pointwise ordering assumption on the two families. This node asserts exactly GeneralCK.FiniteHybridBellman and isolates the remaining Bellman premise of the conditional Courtade–Kumar theorem. The regional and certificate arguments needed to establish the premise remain outstanding; publishing this statement does not prove it.
-- source:
--   New mission-reduction wrapper asserting the unchanged proposition GeneralCK.FiniteHybridBellman; this declaration name is introduced for the upload and is not attributed to an original source theorem. Definition: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/BellmanStatement.lean#L30-L47; conditional transfer: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ConditionalCK.lean#L35-L40

import Definitions.Def_GeneralCK_bellman

theorem GeneralCK.finiteHybridBellman : GeneralCK.FiniteHybridBellman := by sorry
