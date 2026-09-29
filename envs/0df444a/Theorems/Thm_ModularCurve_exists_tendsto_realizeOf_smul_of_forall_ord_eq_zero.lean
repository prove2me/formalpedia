-- Prove2me | Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
-- name    : ModularCurve.exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/8a250c99-95f9-5776-84a4-fa720cc81515
-- title:
--   Cuspidal units have nonzero limits at every cusp
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, and let $F_0$ be an intermediate field of $\mathbb{Q}\subseteq\mathbb{Q}((q))$ assumed equal to [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield generated over $\mathbb{Q}$ by all quotients of the rational Laurent series attached to integral $q$-expansions $p_f,p_g$ of two modular forms $f,g$ of one common weight $k$ on $\Gamma$, with the series of $p_g$ nonzero. Work inside [`ModularCurve.laurentBaseChange ℂ F₀`](def/ModularCurve_LaurentCoeff.html#L103), the intermediate field of $\mathbb{C}\subseteq\mathbb{C}((q))$ generated over $\mathbb{C}$ by the coefficientwise image of $F_0$ under $\mathbb{Q}\to\mathbb{C}$. Let $x$ be a nonzero element of this field, and $y$ an element of it whose underlying Laurent series is [`ModularCurve.jqModC ℂ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image in $\mathbb{C}[[q]]$ of the integral power series $E_4^3\cdot(\text{inverse Dedekind eta unit})$. Assume that for every place $v$ of this field over $\mathbb{C}$ — a valuation subring, distinct from the whole field, containing the image of $\mathbb{C}$ and a principal ideal ring — whose valuation subring does not contain $y$, one has $\mathrm{ord}_v(x)=0$, where $\mathrm{ord}_v$ is minus the logarithm of the associated height-one adic valuation. Then for every $\sigma\in\mathrm{SL}_2(\mathbb{Z})$ there is $L\in\mathbb{C}$, $L\neq 0$, such that $\tau\mapsto \mathrm{realizeOf}_\Gamma(x)(\sigma\cdot\tau)$ tends to $L$ as $\operatorname{Im}\tau\to\infty$; here $\mathrm{realizeOf}_\Gamma(x)(\tau)$ is $g(\tau)/h(\tau)$ for a chosen pair of modular forms $g,h$ of a common weight on $\Gamma$ with $h(\tau)\neq0$ and $x\cdot\widetilde h=\widetilde g$ on $q$-expansions, and $0$ if no such pair exists.
--
--   This is the cuspidal half of the dictionary between the modular curve $X(\Gamma)=\Gamma\backslash\mathfrak{H}^*$ and the places of its function field: a modular function of level $\Gamma$ that is a unit at every place lying over $j=\infty$ has a finite nonzero limit at each cusp $\sigma\infty$. It is used in the construction of the Abel–Jacobi map for $\Gamma_H$-level curves, where divisor classes supported away from the cusps must be represented by functions with controlled behaviour there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero.lean

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

theorem ModularCurve.exists_tendsto_realizeOf_smul_of_forall_ord_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (hF : F₀ = ModularCurve.qExpFunctionFieldC ℚ Γ)
    (x : ModularCurve.laurentBaseChange ℂ F₀) (hx : x ≠ 0)
    (y : ModularCurve.laurentBaseChange ℂ F₀) (hy : (y : LaurentSeries ℂ) = ModularCurve.jqModC ℂ)
    (hord : ∀ v : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ F₀),
      y ∉ v.toValuationSubring → v.ord x = 0)
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane => ModularCurve.realizeOf Γ (x : LaurentSeries ℂ) (σ • τ))
        atImInfty (𝓝 L) := by sorry
