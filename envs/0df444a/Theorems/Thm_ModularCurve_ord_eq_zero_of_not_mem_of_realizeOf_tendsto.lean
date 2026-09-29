-- Prove2me | Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto
-- name    : ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/0d0fa81e-bb59-560b-af21-532b63f8b233
-- title:
--   Modular functions with nonzero cusp limits are units at cuspidal places
-- statement:
--   Let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing $T = \begin{pmatrix}1&1\\0&1\end{pmatrix}$ and satisfying `CongruenceSubgroup.IsCongruenceSubgroup`, and let $F_0$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ attached to integral $q$-expansions $p_f, p_g$ of modular forms $f, g$ of a common weight $k$ for $\Gamma$ (with $\mathrm{intSeriesC}\,p_g \ne 0$). Let $x$ lie in [`ModularCurve.laurentBaseChange ℂ F₀`](def/ModularCurve_LaurentCoeff.html#L103), the subfield of $\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F_0$. Let $F : \mathfrak{H} \to \mathbb{C}$ be such that for every $\tau \in \mathfrak{H}$ the functions $z \mapsto F(\mathrm{ofComplex}\,z)$ and $z \mapsto \mathrm{realizeOf}\,\Gamma\,x\,(\mathrm{ofComplex}\,z)$ agree on a punctured neighbourhood of $\tau$ in $\mathbb{C}$, where $\mathrm{realizeOf}\,\Gamma\,x\,\tau$ is $g(\tau)/h(\tau)$ for a chosen pair of weight-$k$ modular forms $g,h$ for $\Gamma$ with $h(\tau) \ne 0$ and $x \cdot \widehat{h} = \widehat{g}$ on $q$-expansions (and $0$ if no such pair exists). Assume that for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is $L \ne 0$ with $F(\sigma \cdot \tau) \to L$ as $\mathrm{Im}\,\tau \to \infty$. Let $v$ be a place of this field over $\mathbb{C}$, i.e. a valuation subring, not the whole field, containing the image of $\mathbb{C}$ and a principal ideal ring, and let $y$ be the element whose Laurent series is [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image of the power series $E_4^3 \cdot \eta^{-24}$-type numerator `jNum`, so that $y$ is the $q$-expansion of $j$. If $y \notin \mathcal{O}_v$, then $\mathrm{ord}_v(x) = 0$, where $\mathrm{ord}_v$ is minus the logarithm of the adic valuation attached to the height-one prime of $\mathcal{O}_v$.
--
--   This is the statement that a modular function for $\Gamma$ whose associated function on $\mathfrak{H}$ has a finite nonzero limit at every cusp is a unit at every place of the $q$-expansion function field lying over $j = \infty$, no identification of such places with $\Gamma \backslash \mathbb{P}^1(\mathbb{Q})$ being required. It feeds the computation of divisors in the complex place dictionary, being used in the principality criterion via the Abel–Jacobi map and in the construction of field elements with prescribed orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (x : ModularCurve.laurentBaseChange ℂ F₀)
    (F : ℍ → ℂ)
    (hFx : ∀ τ : ℍ, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀))
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hv : y ∉ v.toValuationSubring) :
    v.ord x = 0 := by sorry
