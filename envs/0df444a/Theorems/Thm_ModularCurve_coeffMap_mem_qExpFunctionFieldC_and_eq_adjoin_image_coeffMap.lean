-- Prove2me | Theorems.Thm_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
-- name    : ModularCurve.coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/bb778503-b829-5994-a016-a8f9a918e123
-- title:
--   Base change of the q-expansion function field along ι
-- statement:
--   Let $K$ and $K'$ be fields, let $\iota\colon K\to K'$ be a ring homomorphism, and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$. Write `coeffMap` $\iota$ for the coefficientwise ring homomorphism $K((q))\to K'((q))$ on Laurent series (formal Hahn series over $\mathbb{Z}$), and let `qExpFunctionFieldC` $K\,\Gamma$ be the intermediate field of $K((q))$ generated over $K$ by the set `intFormRatiosC` $K\,\Gamma$ of all quotients $\mathrm{intSeriesC}_K(p_f)/\mathrm{intSeriesC}_K(p_g)$, where for some weight $k\in\mathbb{Z}$ there are modular forms $f,g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and integral power series $p_f,p_g\in\mathbb{Z}[[q]]$ with `IsIntegralQExp` $f\,p_f$ and `IsIntegralQExp` $g\,p_g$ (the predicate tying a form to an integral $q$-expansion), subject to $\mathrm{intSeriesC}_K(p_g)\neq 0$; here $\mathrm{intSeriesC}_K(p)$ is the Laurent series over $K$ obtained from $p$ by coefficientwise base change along $\mathbb{Z}\to K$. The theorem asserts the conjunction of two facts: every element of `qExpFunctionFieldC` $K\,\Gamma$ is carried by `coeffMap` $\iota$ into `qExpFunctionFieldC` $K'\,\Gamma$; and `qExpFunctionFieldC` $K'\,\Gamma$ equals the intermediate field generated over $K'$ by the image under `coeffMap` $\iota$ of (the underlying set of) `qExpFunctionFieldC` $K\,\Gamma$.
--
--   This is the base-change compatibility of the $q$-expansion function field of $X(\Gamma)$ with respect to a change of coefficient field, with no surjectivity or characteristic hypothesis on $\iota$. It is used to compare such function fields over a residue field and over a larger field, in the norm compatibility along the Hecke correspondence [`ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap`](thm.html#ModularCurve.coeffMap_coe_norm_along_heckeAlphaModLH_eq_coe_norm_along_heckeAlphaModLH_coeffMap) and in the degree bound [`ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap`](thm.html#ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap
    (K K' : Type*) [Field K] [Field K'] (ι : K →+* K') (Γ : Subgroup SL(2, ℤ)) :
    (∀ x ∈ qExpFunctionFieldC K Γ, coeffMap ι x ∈ qExpFunctionFieldC K' Γ) ∧
    qExpFunctionFieldC K' Γ =
      IntermediateField.adjoin K' (coeffMap ι '' (qExpFunctionFieldC K Γ : Set (LaurentSeries K))) := by sorry
