-- Prove2me | Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
-- name    : ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/1b573026-f3e5-54f4-9b47-7fdf29f182f5
-- title:
--   Genus invariance of q-expansion function fields under constant extension
-- statement:
--   Let $K_0$ and $K$ be algebraically closed fields, let $\varphi \colon K_0 \to K$ be a ring homomorphism, and let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb{Z})$. For a field $L$, write $F_L =$ [`ModularCurve.qExpFunctionFieldC L Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of the Laurent series field $L((q))$ generated over $L$ by the set of all quotients `intSeriesC L pf / intSeriesC L pg`, where $k \in \mathbb{Z}$, where $f$ and $g$ are modular forms of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}(2,\mathbb{R})$, where $pf, pg$ are power series with integer coefficients satisfying the predicates `IsIntegralQExp f pf` and `IsIntegralQExp g pg` (which relate a form to its integral $q$-expansion), the Laurent series over $L$ attached to an integral power series by `intSeriesC`, and the denominator `intSeriesC L pg` is nonzero. Assume that some $x \in F_{K_0}$ is transcendental over $K_0$ and that $F_{K_0}$ is finite-dimensional over $K_0(x)$. Then [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145) $K$ $F_K$ equals [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145) $K_0$ $F_{K_0}$, where `genusFF L F` is the $L$-dimension of $H^1$ of the zero divisor of $F/L$. Only the function-field hypothesis over $K_0$ is assumed; its analogue over $K$ is not.
--
--   This is the invariance of the genus of a one-variable function field under extension of an algebraically closed constant field, specialised to the function fields cut out by $q$-expansions of modular forms on $\Gamma$. It lets genus computations for modular curves be carried out over one convenient algebraically closed coefficient field and transported to another, and is used in the comparison of the genus of the function field of $X_1(N)$ with that of its Laurent-series base change and in the analysis of regular differentials on $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom
    {K₀ K : Type*} [Field K₀] [Field K] [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hfg : ∃ x : ModularCurve.qExpFunctionFieldC K₀ Γ, Transcendental K₀ x ∧
      FiniteDimensional
        (IntermediateField.adjoin K₀ ({x} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ)) :
    AlgebraicCurve.genusFF K (ModularCurve.qExpFunctionFieldC K Γ) =
      AlgebraicCurve.genusFF K₀ (ModularCurve.qExpFunctionFieldC K₀ Γ) := by sorry
