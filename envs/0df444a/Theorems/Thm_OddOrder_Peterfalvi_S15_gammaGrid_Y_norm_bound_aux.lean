-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_gammaGrid_Y_norm_bound_aux
-- name    : OddOrder.Peterfalvi.S15.gammaGrid_Y_norm_bound_aux
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:22:18.570383+00:00
-- url     : https://prove2.me/theorems/bb43aaee-592b-422d-b8da-1fe94e0c5bca
-- title:
--   Peterfalvi (13.18.d): residual-norm bound $\|Y\|^2\le (u-1)/q$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order (`IsMinimalSimpleOdd G`) with no maximal subgroup of type V, and let `hyp : Hypothesis (G := G)` be the Peterfalvi Section 13 hypothesis package (subgroups $P,U,W_1,W_2,S,\dots$ and parameters $p,q,u,c,\dots$). Assume $c=1$. Let $X,Y$ be class functions on $G$ with $\Gamma=X+Y$ (`GammaGrid hG hyp = X + Y`), $\langle X,Y\rangle=0$, and $\langle Y,\eta_{ik}\rangle=0$ for all $i<q$, $k<p$ (`hyp.eta i k`). Then
--   $$\mathrm{Re}\,\langle Y,Y\rangle\ \le\ \frac{u-1}{q}.$$
--
--   This is the core of the residual-norm bound of Peterfalvi (13.18.d).
--
--   **Formalization Note.** The statement is formulated with the instances scoped by `FiniteInduce`; $u,q\in\mathbb N$ are cast to $\mathbb Q$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacter.lean#L632-L824

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem gammaGrid_Y_norm_bound_aux [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hc1 : hyp.c = 1)
    (X Y : ClassFunction G ℂ) (defXY : GammaGrid hG hyp = X + Y)
    (oXY : ClassFunction.inner X Y = 0)
    (oYeta : ∀ (i : Fin hyp.q) (k : Fin hyp.p), ClassFunction.inner Y (hyp.eta i k) = 0) :
    (ClassFunction.inner Y Y).re ≤ ((hyp.u : ℚ) - 1) / (hyp.q : ℚ) := by sorry

end OddOrder.Peterfalvi.S15
