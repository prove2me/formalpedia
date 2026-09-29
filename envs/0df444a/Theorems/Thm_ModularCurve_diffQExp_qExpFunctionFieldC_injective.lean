-- Prove2me | Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
-- name    : ModularCurve.diffQExp_qExpFunctionFieldC_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/4b9cfa90-2a28-5634-93b0-7fdb6f8b2053
-- title:
--   Injectivity of the q-expansion map on differentials
-- statement:
--   Let $K$ be an algebraically closed field and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index containing the translation matrix `ModularGroup.T`. Let $F =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) be the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the set of all quotients $\mathrm{intSeriesC}_K(p_f)/\mathrm{intSeriesC}_K(p_g)$, where for some weight $k$ there are modular forms $f,g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and integral power series $p_f,p_g$ over $\mathbb{Z}$ that are integral $q$-expansions of $f$ and of $g$ respectively, with the coefficientwise image $\mathrm{intSeriesC}_K(p_g)$ nonzero. The assertion is that the $F$-linear map $\mathrm{diffQExp}\,F : \Omega[F\!\mid\!K] \to K((q))$ is injective, where this map is the universal lift to Kähler differentials of the derivation of $F$ into $K((q))$ obtained by restricting along the inclusion $F \hookrightarrow K((q))$ the derivation `qEuler` of $K((q))$, which multiplies the coefficient of $q^n$ by $n$, i.e. $q\,\mathrm{d}/\mathrm{d}q$. Thus a differential of $F$ over $K$ whose $q$-expansion vanishes is zero.
--
--   This is the injectivity of the $q$-expansion of differentials on the modular curve attached to $\Gamma$ over an algebraically closed coefficient field of arbitrary characteristic, i.e. the statement that a meromorphic differential is determined by the Laurent series $h$ with $\omega = h\,\mathrm{d}q/q$. It underlies the identification of spaces of cusp forms with spaces of differentials on the curve, and is used in the construction of reduction maps onto subspaces of polar differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.diffQExp_qExpFunctionFieldC_injective
    (K : Type*) [Field K] [IsAlgClosed K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) :
    Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K Γ)) := by sorry
