-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_indPW1_apply_eq_one_of_mem_W1_sharp
-- name    : OddOrder.Peterfalvi.S15.indPW1_apply_eq_one_of_mem_W1_sharp
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:16:34.556471+00:00
-- url     : https://prove2.me/theorems/63f26790-2b43-4ccd-9ea6-fbdc9fb94fe3
-- title:
--   Peterfalvi (13.18.a): $\mathrm{Ind}_{PW_1}^S1$ equals $1$ on $W_1^\#$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order and `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package, with subgroups $P,W_1,S\le G$. Let $x\in S$ with $x\in W_1$ and $x\neq1$. Then the induced character `indPW1 hyp`, which is $\mathrm{Ind}_{PW_1}^{S}1$, satisfies
--   $$\mathrm{Ind}_{PW_1}^{S}1\,(x)=1 .$$
--
--   This is Peterfalvi (13.18.a), the value on $W_1^\#$ of the induced trivial character, obtained by passing to $S/P\cong U\rtimes W_1$ and using the Frobenius complement value.
--
--   **Formalization Note.** The statement is formulated for the scoped `FiniteInduce` instances. `indPW1 hyp` is a class function on $\uparrow S$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacterBasic.lean#L400-L511

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs in
open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem indPW1_apply_eq_one_of_mem_W1_sharp [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {x : ↥hyp.S} (hxW1 : (x : G) ∈ hyp.W1) (hx1 : x ≠ 1) :
    indPW1 hyp x = 1 := by sorry

end OddOrder.Peterfalvi.S15
