-- Prove2me | Theorems.Thm_ModularCurve_exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf
-- name    : ModularCurve.exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/f8d8616a-dfb9-5303-95c1-39d6175869af
-- title:
--   Cusp places of ℂ·ℚ(X(Γ)) are exhausted by Pl
-- statement:
--   Let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index which contains the translation matrix `ModularGroup.T` and satisfies the predicate `CongruenceSubgroup.IsCongruenceSubgroup`, and let $F_0$ be an intermediate field of $\mathbb Q\subset\mathbb Q((q))$ equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield generated over $\mathbb Q$ by the quotients $p_f/p_g$ of integral $q$-expansions of pairs of modular forms of level $\Gamma$ and equal weight (with $p_g\ne 0$). Write $F$ for [`ModularCurve.laurentBaseChange ℂ F₀`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $\mathbb C((q))$ generated over $\mathbb C$ by the image of $F_0$ under coefficientwise extension of scalars. Let $y\in F$ have Laurent series [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), that is $q^{-1}$ times the power series $E_4^3\cdot\eta^{-24}$-type numerator `jNum` pushed to $\mathbb C$. Let $\mathrm{Pl}$ assign to each $\sigma\in \mathrm{SL}_2(\mathbb Z)$ a place of $F/\mathbb C$ in the sense of [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) (a proper valuation subring of $F$ containing $\mathbb C$ whose ring is a principal ideal ring), subject to two hypotheses: $\mathrm{Pl}(\gamma\sigma)=\mathrm{Pl}(\sigma)$ for all $\gamma\in\Gamma$ and all $\sigma$; and for every $\sigma$ and every nonzero $x\in F$ with $\operatorname{ord}_{\mathrm{Pl}(\sigma)}x=0$ (the negated logarithm of the associated adic valuation) there is $L\ne 0$ such that $\tau\mapsto$ [`ModularCurve.realizeOf`](def/ModularCurve_ComplexPlaceDictionaryOf.html#L15) $\Gamma\,x\,(\sigma\cdot\tau)$ tends to $L$ as $\operatorname{Im}\tau\to\infty$, where `realizeOf` evaluates $x$ at $\tau$ as $f(\tau)/g(\tau)$ for some choice of modular forms $f,g$ of level $\Gamma$ and equal weight with $g(\tau)\ne0$ and $x\cdot q\text{-exp}(g)=q\text{-exp}(f)$, and is $0$ if no such pair exists. Then every place $P$ of $F/\mathbb C$ with $y\notin P$ is of the form $\mathrm{Pl}(\sigma)$ for some $\sigma\in\mathrm{SL}_2(\mathbb Z)$.
--
--   This is the completeness half of the dictionary between cusps of $X(\Gamma)$ and places of its function field: the places at which the $j$-expansion fails to be integral, i.e. the cusp places, are exactly those produced by the family $\mathrm{Pl}$ indexed by right $\Gamma$-cosets in $\mathrm{SL}_2(\mathbb Z)$. It is used in the divisor-theoretic analysis of $q$-expansions at cusps, notably in computing orders of vanishing in terms of cusp widths.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_apply_eq_of_forall_ord_eq_zero_tendsto_realizeOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (y : ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (Pl : SL(2, ℤ) → AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀))
    (hΓPl : ∀ γ ∈ Γ, ∀ σ : SL(2, ℤ), Pl (γ * σ) = Pl σ)
    (hlim : ∀ (σ : SL(2, ℤ)) (x : ↥(ModularCurve.laurentBaseChange ℂ F₀)), x ≠ 0 → (Pl σ).ord x = 0 →
      ∃ L : ℂ, L ≠ 0 ∧
        Filter.Tendsto (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ))
          UpperHalfPlane.atImInfty (nhds L))
    (P : AlgebraicCurve.Place ℂ ↥(ModularCurve.laurentBaseChange ℂ F₀)) (hP : y ∉ P.toValuationSubring) :
    ∃ σ : SL(2, ℤ), Pl σ = P := by sorry
