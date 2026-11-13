-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_indPW1_inner_self_aux
-- name    : OddOrder.Peterfalvi.S15.indPW1_inner_self_aux
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:16:31.021089+00:00
-- url     : https://prove2.me/theorems/80cec208-7304-43fa-84c0-f5be52a9c08a
-- title:
--   Peterfalvi (13.18.b): $\|\mathrm{Ind}_{PW_1}^S1\|^2=(u-1)/q+1$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order and `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package with $c=1$ (`hyp.c = 1`). Then
--   $$\big\langle\mathrm{Ind}_{PW_1}^{S}1,\ \mathrm{Ind}_{PW_1}^{S}1\big\rangle_S=\frac{u-1}{q}+1 ,$$
--   where $u=$ `hyp.u`, $q=$ `hyp.q`, and the left side is the inner product of `indPW1 hyp` with itself.
--
--   This is the Frobenius half of Peterfalvi (13.18.b).
--
--   **Formalization Note.** The statement is for the scoped `FiniteInduce` instances; the right side is a rational number cast to $\mathbb C$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean#L262-L379

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem indPW1_inner_self_aux [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1) :
      ClassFunction.inner (indPW1 hyp) (indPW1 hyp)
        = ((((hyp.u : ℚ) - 1) / (hyp.q : ℚ) + 1 : ℚ) : ℂ) := by sorry

end OddOrder.Peterfalvi.S15
