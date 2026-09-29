-- Prove2me | Theorems.Thm_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg
-- name    : ModularCurve.exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/dfe6dbba-17ba-5d70-8a65-70ccae126c71
-- title:
--   Exponential decay at cusps of cusp-regular differentials
-- statement:
--   Let $\Gamma\le SL_2(\mathbb Z)$ be of finite index with $T\in\Gamma$, and let $F_0$ be an intermediate field of $\mathbb Q\subseteq\mathbb Q((q))$ which is assumed equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the quotients of integral $q$-expansions of pairs of modular forms of equal weight on $\Gamma$. Write $F=$ [`ModularCurve.laurentBaseChange ℂ F₀`](def/ModularCurve_LaurentCoeff.html#L103) for the subfield of $\mathbb C((q))$ generated over $\mathbb C$ by the image of $F_0$ under coefficientwise extension of scalars, and assume that every place $w$ of $F/\mathbb C$ — a valuation subring of $F$ containing $\mathbb C$, proper, and a principal ideal ring — satisfies `DCoordGenerates`, i.e. $D_{\mathbb C}(\pi_w)$ spans $\Omega_{F/\mathbb C}$ over $F$, where $\pi_w$ is the chosen uniformiser. Let $a,x,y\in F$ with $y$ equal, as a Laurent series, to [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image of the power series $E_4^3\cdot\eta^{-24}$-numerator `jNum`. Assume that for every place $v$ with $y\notin v$ one has $\operatorname{ord}_v\ge 0$ of the coefficient of $a\,D_{\mathbb C}x$ with respect to $D_{\mathbb C}(\pi_v)$. Then for every $\sigma\in SL_2(\mathbb Z)$ there is $\delta>0$ such that the weight-$2$ slash by $\sigma$ of $\tau\mapsto \tilde a(\tau)\,\tilde x'(\tau)$ is $O(e^{-\delta\operatorname{Im}\tau})$ along `atImInfty`; here $\tilde z=$ [`ModularCurve.realizeOf Γ z`](def/ModularCurve_ComplexPlaceDictionaryOf.html#L15) is the function on $\mathfrak H$ obtained by choosing modular forms $g,h$ of some common weight on $\Gamma$ with $z\cdot q\text{-exp}(h)=q\text{-exp}(g)$ and $h(\tau)\neq0$ and evaluating $g/h$ (and $0$ if no such data exist), and $\tilde x'$ is the complex derivative of $\tilde x$ in $\tau$.
--
--   This is the analytic regularity statement at the cusps: a differential $a\,dx$ on the curve with function field $\mathbb C\cdot F_0$ which is regular at all places not containing $j$ pulls back to a weight-two meromorphic function on $\mathfrak H$ whose $\sigma$-translates all decay exponentially, i.e. vanish at every cusp. It feeds the construction of slash-invariant objects with prescribed non-vanishing residue in [`ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH`](thm.html#ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    [∀ w : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀), w.DCoordGenerates]
    (a x : ModularCurve.laurentBaseChange ℂ F₀)
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hreg : ∀ v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀), y ∉ v.toValuationSubring →
      0 ≤ v.ordDifferential (a • KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ F₀) x))
    (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun τ : ℍ => ModularCurve.realizeOf Γ (a : LaurentSeries ℂ) τ *
          deriv (fun w : ℂ => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (ofComplex w)) τ)
        ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im) := by sorry
