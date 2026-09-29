-- Prove2me | Theorems.Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
-- name    : HeckeEis.coeff_single_one_eq_eval_of_mem_binaryForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/0e2ead68-eae4-581f-bf18-2e1442075acd
-- title:
--   X₁ⁿ-coefficient of a binary form as its value at (0,1)
-- statement:
--   Let $K$ be a commutative ring, let $n$ be a natural number, and let $P$ be a polynomial in the two variables indexed by `Fin 2` over $K$, i.e. $P \in K[X_0,X_1]$. Assume $P$ belongs to [`HeckeEis.BinaryForm K n`](def/HeckeEis_BinaryFormRep.html#L25), which is by definition the $K$-submodule `MvPolynomial.homogeneousSubmodule (Fin 2) K n` of polynomials homogeneous of degree $n$: every monomial occurring in $P$ has total degree $n$ (the zero polynomial being included). The conclusion is the equality, in $K$, of two quantities: the coefficient of $P$ at the exponent vector `Finsupp.single 1 n`, that is the coefficient of the monomial $X_1^{\,n}$, and the evaluation of $P$ at the point given by the vector `![0, 1]`, i.e. the substitution $X_0 \mapsto 0$, $X_1 \mapsto 1$. Thus for a binary form of degree $n$ one has $\operatorname{coeff}_{X_1^n}(P) = P(0,1)$.
--
--   This identifies the linear functional 'leading $X_1^n$-coefficient' on degree-$n$ binary forms with evaluation at the point $(0:1)$, which in the row-vector convention used for the representation of $\mathrm{SL}_2$ on binary forms is the cusp at infinity and is fixed by the upper triangular unipotent matrices. It is used in the computations with Eichler integrals and with coefficient cocycles, for instance by [`HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash`](thm.html#HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash), [`HeckeEis.IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range`](thm.html#HeckeEis.IsEichlerIntegral.vadd_sub_T_zpow_apply_mem_range) and [`HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles`](thm.html#HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.coeff_single_one_eq_eval_of_mem_binaryForm {K : Type*} [CommRing K] {n : ℕ}
    {P : MvPolynomial (Fin 2) K} (hP : P ∈ HeckeEis.BinaryForm K n) :
    MvPolynomial.coeff (Finsupp.single 1 n) P = MvPolynomial.eval ![0, 1] P := by sorry
