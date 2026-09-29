-- Prove2me | Theorems.Thm_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion
-- name    : ModularCurve.one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/784d0a4c-4ce1-582c-a3b6-6ad757b941e7
-- title:
--   Order bound at a cusp for the coefficient of ω_f = y dj
-- statement:
--   Let $N \geq 1$, let $\sigma : \overline{\mathbb{Q}} \to \mathbb{C}$ be a ring homomorphism from the algebraic closure of $\mathbb{Q}$, and let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$. Let $y$ be a nonzero element of `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise image, under the map `coeffEmb` induced by $\mathbb{Q} \to \overline{\mathbb{Q}}$, of `modularFunctionFieldFull N` (itself the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by `divisorExpansions N`). Write $\bar j \in \overline{\mathbb{Q}}((q))$ for the coefficientwise image of the Laurent series `jq` $= q^{-1}\cdot$`jNumQ`; it lies in that field. Assume that applying the coefficientwise map induced by $\sigma$ to $y \cdot \theta(\bar j)$, where $\theta(x) = q\,\frac{d}{dq}x$ is given by `thetaL`, yields the $q$-expansion `qExpansion 1 (f : ℍ → ℂ)` of $f$, viewed in $\mathbb{C}((q))$. Let $w$ be a place of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ in the sense of the project structure `Place` (a valuation subring containing $\overline{\mathbb{Q}}$, proper, and a principal ideal ring), with integer-valued order function `Place.ord`, and assume $\operatorname{ord}_w(\bar j) < 0$. Then $1 - \operatorname{ord}_w(\bar j) \leq \operatorname{ord}_w(y)$.
--
--   This is the regularity of the differential $\omega_f = y\,d\bar j$ attached to a weight-$2$ cusp form at the places of the geometric function field of $X_0(N)$ lying over $j = \infty$, i.e. at the cusps: if $h = -\operatorname{ord}_w(\bar j)$ is the ramification index over the $j$-line, the assertion is $\operatorname{ord}_w(y) \geq h+1$, exactly compensating $\operatorname{ord}_w(d\bar j) = -h-1$. It feeds into the statement that $\omega_f$ is a regular differential on $X_0(N)$ over $\overline{\mathbb{Q}}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane ModularCurve AlgebraicCurve

theorem ModularCurve.one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion (N : ℕ) [NeZero N]
    (σ : AlgebraicClosure ℚ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (y : modularFunctionFieldBar N) (hy0 : y ≠ 0)
    (hy : coeffMap σ ((y : LaurentSeries (AlgebraicClosure ℚ)) *
        thetaL (AlgebraicClosure ℚ) (coeffEmb (AlgebraicClosure ℚ) jq)) =
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hw : w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) < 0) :
    1 - w.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
          modularFunctionFieldBar N) ≤ w.ord y := by sorry
