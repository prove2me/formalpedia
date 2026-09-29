-- Prove2me | Theorems.Thm_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
-- name    : ModularCurve.exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/7370d638-21ce-5968-a661-67c17745520c
-- title:
--   Cusp limits transfer from F to the ratio g/h
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix $T$, and let $g,h$ be modular forms of one and the same integer weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$, with $h \neq 0$. Let $x$ be a Laurent series over $\mathbb{C}$ whose product with the $q$-expansion of $h$ of period $1$, viewed as a Laurent series, equals the $q$-expansion of $g$ of period $1$. Let $F : \mathfrak{H} \to \mathbb{C}$ be a function such that for every $\tau \in \mathfrak{H}$ the functions $z \mapsto F(\mathrm{ofComplex}\, z)$ and $z \mapsto \mathrm{realizeOf}\,\Gamma\,x\,(\mathrm{ofComplex}\, z)$ agree on a punctured neighbourhood of $\tau$ in $\mathbb{C}$; here $\mathrm{realizeOf}\,\Gamma\,x\,\tau$ is $g_0(\tau)/h_0(\tau)$ for some choice of weight $k_0$ and modular forms $g_0,h_0$ of weight $k_0$ for $\Gamma$ with $h_0(\tau) \neq 0$ and $x$ times the $q$-expansion of $h_0$ equal to that of $g_0$, if such data exist, and $0$ otherwise. Assume furthermore that for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ the function $\tau \mapsto F(\sigma \cdot \tau)$ tends to some non-zero limit as $\operatorname{Im} \tau \to \infty$. Then for each given $\sigma \in \mathrm{SL}_2(\mathbb{Z})$ there is $L \neq 0$ with $g(\sigma \cdot \tau)/h(\sigma \cdot \tau) \to L$ as $\operatorname{Im}\tau \to \infty$.
--
--   This is the transfer of cusp behaviour from a function $F$ that agrees off a discrete set with the level-$\Gamma$ realization of a Laurent series to the honest ratio $g/h$ of modular forms representing that series: finite non-zero limits towards $i\infty$ in every $\mathrm{SL}_2(\mathbb{Z})$-translate persist. It is used in the computation of orders of vanishing of such realizations, via [`ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto`](thm.html#ModularCurve.ord_eq_zero_of_not_mem_of_realizeOf_tendsto), and rests on the identification [`ModularCurve.realizeOf_eq_div`](thm.html#ModularCurve.realizeOf_eq_div) of the realization with $g/h$ away from the zeros of $h$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto.lean

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.exists_tendsto_div_smul_of_eventuallyEq_realizeOf_of_tendsto
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (F : UpperHalfPlane → ℂ)
    (hFx : ∀ τ : UpperHalfPlane, (fun z : ℂ => F (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z : ℂ => ModularCurve.realizeOf Γ x (ofComplex z))
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) atImInfty (𝓝 L))
    (σ : SL(2, ℤ)) :
    ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => (g : UpperHalfPlane → ℂ) (σ • τ) / (h : UpperHalfPlane → ℂ) (σ • τ))
        atImInfty (𝓝 L) := by sorry
