-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S12_Hypothesis_alignedOmegaSigmaGrid_apply_eq_sourceCharacter
-- name    : OddOrder.Peterfalvi.S12.Hypothesis.alignedOmegaSigmaGrid_apply_eq_sourceCharacter
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:17:30.56423+00:00
-- url     : https://prove2.me/theorems/61a3f148-47f1-40f4-8281-437e4126623e
-- title:
--   On the type-$P$ regular set the aligned $\sigma$-grid entry equals its source character
-- statement:
--   Let $G$ be a finite minimal simple odd-order group (`hG`), $M\le G$ a subgroup, `hyp : S12.Hypothesis M` the Peterfalvi Section 12 hypothesis with parameters $w_1,w_2$, and `hodd : Odd (Nat.card G)`. Let $i<w_1$, $j<w_2$, and let $v\in G$ lie in the type-$P$ regular set `typePV M hyp.typeP` (with `hv.1` the membership of $v$ in the underlying subgroup). Then
--   $$\texttt{hyp.alignedOmegaSigmaGrid hG hodd i j}\ (v) \;=\; \bigl(\texttt{hyp.alignedOmegaSourceCharacter hG hodd i j}\ \langle v,\ \cdot\rangle\bigr),$$
--   that is, the value at $v$ of the aligned $\sigma$-grid class function on $G$ equals the value, viewed in $\mathbb{C}$, of the underlying multiplicative character (a unit of $\mathbb{C}$) evaluated at the subgroup element corresponding to $v$.
--
--   This is the source-side counterpart of `tau3_apply_of_regular` and restores the multiplicative character on the regular set.
--
--   **Formalization Note.** `alignedOmegaSourceCharacter … i j : _ → ℂˣ` takes a subtype element `⟨v, hv.1⟩`; its value is coerced to $\mathbb{C}$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapNonorthogonality.lean#L680-L734

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapMemberResidual
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapNonorthogonality

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in

theorem Hypothesis.alignedOmegaSigmaGrid_apply_eq_sourceCharacter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) {v : G}
    (hv : v ∈ typePV M hyp.typeP) :
    hyp.alignedOmegaSigmaGrid hG hodd i j v =
      ((hyp.alignedOmegaSourceCharacter hG hodd i j
        ⟨v, hv.1⟩ : ℂˣ) : ℂ) := by sorry

end OddOrder.Peterfalvi.S12
