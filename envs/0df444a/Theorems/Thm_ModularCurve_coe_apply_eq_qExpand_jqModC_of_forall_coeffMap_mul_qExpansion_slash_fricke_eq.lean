-- Prove2me | Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
-- name    : ModularCurve.coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/1f4c9d7d-695a-5db3-aa75-50413a1420d9
-- title:
--   Fricke-type automorphism sends j(q) to j(qⁿ)
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$, let $n$ be a nonzero natural number, let $\iota : \overline{\mathbb Q} \to \mathbb C$ be a ring homomorphism, and let $W \in \mathrm{GL}_2(\mathbb R)$ have underlying matrix $\begin{pmatrix}0&-1\\ n&0\end{pmatrix}$. Write $F_{\mathbb Q} =$ [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101) for the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the ratios $\mathrm{intSeriesC}\,\mathbb Q\,p_f / \mathrm{intSeriesC}\,\mathbb Q\,p_g$, taken over all weights $k \in \mathbb Z$ and all modular forms $f, g$ of weight $k$ for $\Gamma$ regarded inside $\mathrm{GL}_2(\mathbb R)$ together with integral power series $p_f, p_g$ satisfying the predicate `IsIntegralQExp` for $f$ and for $g$ and with $\mathrm{intSeriesC}\,\mathbb Q\,p_g \neq 0$; and let $F =$ `laurentBaseChange` of $F_{\mathbb Q}$, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the image of $F_{\mathbb Q}$ under the coefficientwise map $\mathbb Q((q)) \to \overline{\mathbb Q}((q))$. Let $w$ be a $\overline{\mathbb Q}$-algebra automorphism of $F$ with the following property: for every $x \in F$, every $k \in \mathbb Z$ and all modular forms $f, g$ of weight $k$ for $\Gamma$, if the coefficientwise image of $x$ under $\iota$ times the width-$1$ $q$-expansion of $g$ equals the width-$1$ $q$-expansion of $f$ (as Laurent series over $\mathbb C$), then the coefficientwise image of $w x$ under $\iota$ times the width-$1$ $q$-expansion of $g \mid_k W$ equals the width-$1$ $q$-expansion of $f \mid_k W$. Let $jx \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15) over $\overline{\mathbb Q}$, that is $q^{-1}$ times the image of the integral power series $E_4^3 \cdot \eta^{-24}$-type numerator `jNum`. Then the Laurent series underlying $w(jx)$ is [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25) at $n$ applied to `jqModC`, i.e. the series obtained from $j(q)$ by multiplying all exponents by $n$, namely $j(q^n)$.
--
--   This is the statement that an automorphism acting on $q$-expansions through the weight-$k$ slash by the Fricke-type matrix $\begin{pmatrix}0&-1\\ n&0\end{pmatrix}$ carries the modular invariant $j(q)$ to $j(q^n)$, the identification being made via the factorisation of that matrix through $S$ and $\mathrm{diag}(n,1)$ and the level-one identity $j = E_4^3/\Delta$. It is used in the construction of a pair of automorphisms of the $q$-expansion function field intertwining the Hecke correspondences and compatible with the Fricke slash.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
    (Γ : Subgroup SL(2, ℤ)) (n : ℕ) [NeZero n] (ι : AlgebraicClosure ℚ →+* ℂ)
    (W : GL (Fin 2) ℝ) (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (n : ℝ), 0])
    (w : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≃ₐ[AlgebraicClosure ℚ]
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hS : ∀ (x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) (k : ℤ)
        (f g : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        ModularCurve.coeffMap ι ((w x : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
              LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)))
    (jx : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hjx : (jx : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    ((w jx : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qExpand (AlgebraicClosure ℚ) n (ModularCurve.jqModC (AlgebraicClosure ℚ)) := by sorry
