-- Prove2me | Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1
-- name    : ModularCurve.isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/b51596c5-4aed-52ae-9d37-c0c2d6a8e142
-- title:
--   K·ℚ(X₁(M)) is a curve over K
-- statement:
--   Let $K$ be a field of characteristic zero (an algebra over $\mathbb{Q}$) that is algebraically closed, and let $M$ be a positive natural number. Consider first the intermediate field $\mathbb{Q} \subseteq \mathtt{qExpFunctionFieldC}\ \mathbb{Q}\ \Gamma_1(M) \subseteq \mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ the set of all Laurent series of the form $\mathrm{intSeriesC}\,\mathbb{Q}\,p_f / \mathrm{intSeriesC}\,\mathbb{Q}\,p_g$, where $f,g$ are modular forms of some common weight $k$ for the image of $\Gamma_1(M)$ in $\mathrm{GL}_2(\mathbb{R})$ whose $q$-expansions are given by integral power series $p_f,p_g$ (in the sense of `IsIntegralQExp`) with $\mathrm{intSeriesC}\,\mathbb{Q}\,p_g \neq 0$. Let $F_K := \mathtt{laurentBaseChange}\,K$ of this field, namely the intermediate field of $K((q))$ generated over $K$ by the image of that field under the coefficientwise ring homomorphism $\mathbb{Q}((q)) \to K((q))$ induced by $\mathbb{Q} \to K$. The assertion is that $F_K$ satisfies [`AlgebraicCurve.IsCurveOver K`](def/AlgebraicCurve_IsCurveOver.html#L15), i.e.: every nonzero $f \in F_K$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ of $F_K/K$ (a proper valuation subring of $F_K$ containing $K$ which is a principal ideal ring) and with $\deg D = 0$; each such place has residue field finite-dimensional over $K$; and the module of Kähler differentials $\Omega_{F_K/K}$ is free of rank $1$ over $F_K$.
--
--   This identifies the base-changed $q$-expansion function field of $X_1(M)$ as a curve in the project's axiomatic sense, the setting in which places, divisors, degrees and differentials of $X_1(M)$ over an algebraically closed field of characteristic zero are manipulated. It is the input to the finiteness of Riemann–Roch spaces for $F_K$, to the construction of the divisor attached to the weight floor, and to the description of points of $X_1(p)$ in terms of the divisor class group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve CongruenceSubgroup AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.isCurveOver_laurentBaseChange_qExpFunctionFieldC_gamma1
    (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K] (M : ℕ) [NeZero M] :
    AlgebraicCurve.IsCurveOver K ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))) := by sorry
