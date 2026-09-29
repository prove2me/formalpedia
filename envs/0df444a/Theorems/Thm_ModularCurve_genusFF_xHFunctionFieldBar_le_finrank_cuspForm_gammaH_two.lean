-- Prove2me | Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two
-- name    : ModularCurve.genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/8da32d6e-046c-5b77-ad73-dad82ff67727
-- title:
--   Genus of X_H(M) at most dim_ℂ S₂(Γ_H(M))
-- statement:
--   Let $M$ be a non-zero natural number and let $H$ be a subgroup of the unit group $(\mathbb{Z}/M\mathbb{Z})^\times$. Two numbers are compared. On the left, $\mathrm{genusFF}$ of the extension $\overline{\mathbb{Q}} \subseteq \mathrm{xHFunctionFieldBar}\,M\,H$, that is, the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor (the répartition genus) of the intermediate field of $\overline{\mathbb{Q}}((q))$ obtained by base change: the subfield generated over $\overline{\mathbb{Q}}$ by the image, under the coefficientwise embedding $\mathbb{Q}((q)) \to \overline{\mathbb{Q}}((q))$, of the rational $q$-expansion function field `xHFunctionFieldC ℚ M H`. On the right, the $\mathbb{C}$-dimension of the space of weight-$2$ cusp forms for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(M)$ whose lower-right entry, a unit of $\mathbb{Z}/M\mathbb{Z}$ with inverse the reduction of the upper-left entry, lies in $H$; equivalently $\Gamma_H(M)$. The assertion is the inequality $\mathrm{genusFF} \le \dim_{\mathbb{C}} S_2(\Gamma_H(M))$.
--
--   This is one half of the classical identity $\dim_{\mathbb{C}} S_2(\Gamma_H(M)) = g(X_H(M))$, the direction obtained from an injection of the genus-computing space of regular differentials into weight-$2$ cusp forms; only this inequality is needed downstream. It is used in the dimension count behind the two-component $q$-expansion comparison, [`ModularCurve.finrank_tensorProduct_intTwoCuspForms_eq_finrank_twoCompRegularDifferentials`](thm.html#ModularCurve.finrank_tensorProduct_intTwoCuspForms_eq_finrank_twoCompRegularDifferentials).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.genusFF_xHFunctionFieldBar_le_finrank_cuspForm_gammaH_two
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) ≤
      Module.finrank ℂ (CuspForm (CohCarrier.GammaH M H) 2) := by sorry
