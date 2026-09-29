-- Prove2me | Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
-- name    : ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/0ea85ff3-dbf6-52fc-90f2-4818e4b255c7
-- title:
--   j transcendental and K/L(j) finite separable at level (N,H)
-- statement:
--   Let $N\ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/N)^{\times}$, and let $L$ be a field of characteristic $0$. Let $K$ be an intermediate field of $L(\!(q)\!)=\mathrm{LaurentSeries}\,L$ over $L$ which is assumed to equal [`ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L(\!(q)\!)$ generated over $L$ by the image of the field [`ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH N H)`](def/ModularCurve_X1.html#L101) $\subseteq \mathbb{Q}(\!(q)\!)$ under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81), the ring homomorphism applying $\mathbb{Q}\to L$ to each Laurent coefficient. Let $A$ be a domain equipped with an $L$-algebra structure realising $L$ as its fraction field, and with an $A$-algebra structure on $K$ compatible with that of $L$ via the scalar tower. Finally let $j\in K$ be an element whose image in $L(\!(q)\!)$ is `coeffEmb L ModularCurve.jq`, where `jq` is $q^{-1}$ times the power series `jNumQ` with rational coefficients. The conclusion is threefold: $j$ is transcendental over $A$; $K$ is finite-dimensional over the intermediate field $L(j)$ obtained by adjoining $j$ to $L$ inside $K$; and $K$ is separable over $L(j)$.
--
--   This is the classical statement that the function field of the modular curve $X_H(N)$, with constants extended to an arbitrary field of characteristic $0$, is a finite separable extension of the rational function field in $j$, together with the transcendence of $j$. It is the level- and constant-field-generic form of the statement used when the function field of $X_H(N)$ is compared with integral models, and it feeds the analysis of branch primes and Drinfeld charts in the full-level constructions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.transcendental_and_finiteDimensional_and_isSeparable_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange_xHFunctionField_of_charZero
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField N H))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    Transcendental A j ∧
    FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K ∧
    Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by sorry
