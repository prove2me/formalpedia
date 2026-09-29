-- Prove2me | Theorems.Thm_MvFormalGroup_mem_firstOrderCocycles_iff
-- name    : MvFormalGroup.mem_firstOrderCocycles_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/35268dc6-bd72-54f7-8feb-143995c29cdc
-- title:
--   First-order cocycles as symmetric solutions of linearised associativity
-- statement:
--   Let $k$ be a field, $d$ a natural number, and $G_0$ a $d$-dimensional formal group law over $k$: a tuple $(G_{0,i})_{i<d}$ of power series in the $2d$ variables indexed by $\mathrm{Fin}\,d \sqcup \mathrm{Fin}\,d$ (written $X,Y$) with zero constant term, linear coefficients $\delta_{ij}$ in each block, and satisfying associativity; assume $G_0$ commutative, i.e. invariant under interchanging the two blocks of variables. Let $z=(z_l)_{l<d}$ be a tuple of power series in the same $2d$ variables. Then $z$ lies in `firstOrderCocycles G₀`, the $k$-span of the tuples of coefficientwise $\varepsilon$-parts `epsPart` of those $D :$ `Deformation G₀ (DualNumber k)` whose law `D.F` is commutative, if and only if: each $z_l$ has zero constant term; for all $l,j$ the coefficients of $X_j$ and of $Y_j$ in $z_l$ vanish; each $z_l$ is invariant under swapping the two blocks of variables; and, in the $3d$ variables $X,Y,Z$, $$z_l(G_0(X,Y),Z)+\sum_i z_i(X,Y)\,(\partial_{X_i}G_{0,l})(G_0(X,Y),Z)=z_l(X,G_0(Y,Z))+\sum_i z_i(Y,Z)\,(\partial_{Y_i}G_{0,l})(X,G_0(Y,Z))$$ for every $l$, where the partial derivatives are the coefficientwise operators `pderivLin` in the first, respectively second, block of variables. In particular the span imposes nothing beyond these identities.
--
--   This is the identity-level description of the space of first-order (symmetric) deformation cocycles of a commutative formal group law: a tuple is an $\varepsilon$-part of a commutative deformation over $k[\varepsilon]$ exactly when it is normalised, symmetric and satisfies the linearised associativity (2-cocycle) relation. It is used in the construction of shifted deformations, in [`MvFormalGroup.Deformation.existsUnique_isShiftBy`](thm.html#MvFormalGroup.Deformation.existsUnique_isShiftBy) and [`MvFormalGroup.Deformation.exists_isComm_isShiftBy`](thm.html#MvFormalGroup.Deformation.exists_isComm_isShiftBy), via the square-zero substitution expansion [`MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv`](thm.html#MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_mem_firstOrderCocycles_iff.lean

import Mathlib
import Definitions.Def_MvFormalGroup_FirstOrderDeformation
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries MvFormalGroup

theorem MvFormalGroup.mem_firstOrderCocycles_iff
    {k : Type} [Field k] {d : ℕ} (G₀ : MvFormalGroup d k) [G₀.IsComm]
    (z : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :
    let XY : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun l => X (Sum.inl l)) (fun l => X (Sum.inr (Sum.inl l)))
    let YZ : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun l => X (Sum.inr (Sum.inl l))) (fun l => X (Sum.inr (Sum.inr l)))
    let famL : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun j => subst XY (G₀.toPowerSeries j)) (fun j => X (Sum.inr (Sum.inr j)))
    let famR : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
      Sum.elim (fun j => X (Sum.inl j)) (fun j => subst YZ (G₀.toPowerSeries j))
    z ∈ firstOrderCocycles G₀ ↔
      ((∀ l, constantCoeff (z l) = 0) ∧
       (∀ l j, coeff (Finsupp.single (Sum.inl j) 1) (z l) = 0 ∧ coeff (Finsupp.single (Sum.inr j) 1) (z l) = 0) ∧
       (∀ l, subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) fun j => X (Sum.inl j)) (z l) = z l) ∧
       (∀ l, subst famL (z l) + ∑ i, subst XY (z i) * subst famL (pderivLin (Sum.inl i) (G₀.toPowerSeries l))
            = subst famR (z l) + ∑ i, subst YZ (z i) * subst famR (pderivLin (Sum.inr i) (G₀.toPowerSeries l)))) := by sorry
