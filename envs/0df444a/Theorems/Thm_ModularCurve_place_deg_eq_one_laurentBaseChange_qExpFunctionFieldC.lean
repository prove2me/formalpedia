-- Prove2me | Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
-- name    : ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9c4a97b5-e19e-5d85-8433-53f8068666ed
-- title:
--   Places of L·ℚ(X(Γ)) have degree one
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and assumed algebraically closed, and let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}(2,\mathbb{Z})$ containing the matrix $T = \left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$. Let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ assumed equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of the Laurent series field generated over $\mathbb{Q}$ by the set of quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$, where for some weight $k$ the forms $f, g$ are modular forms for the image of $\Gamma$ in $\mathrm{GL}(2,\mathbb{R})$ whose $q$-expansions are given by integral power series $p_f, p_g$ (predicate `IsIntegralQExp`) with $\mathrm{intSeriesC}(p_g) \neq 0$. Let $E =$ `laurentBaseChange L F₀` be the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise ring map $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. Finally let $W$ be a place of $E$ over $L$, i.e. a valuation subring of $E$ that contains the image of $L$, is not all of $E$, and is a principal ideal ring. Then $\deg W = 1$, where $\deg W$ is the $L$-dimension of the residue field of that valuation subring.
--
--   This is the statement that, over an algebraically closed field of characteristic zero, every place of the base-changed $q$-expansion function field of $X(\Gamma)$ has residue field the field of constants. It is the input that lets places of this field be treated as geometric points, and is used by the complex place dictionary for $X(\Gamma)$ and in the divisor computations attached to Hecke correspondences at a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (W : AlgebraicCurve.Place L ↥(ModularCurve.laurentBaseChange L F₀)) :
    W.deg = 1 := by sorry
