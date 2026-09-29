-- Prove2me | Theorems.Thm_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
-- name    : ModPForms.ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/7bc85531-29c4-56dd-a30f-01b3c826cc18
-- title:
--   The power-series and Laurent-series forms of q d/dq agree
-- statement:
--   Let $K$ be a field and let $\varphi \in K[[q]]$ be a formal power series. Two operators are compared. On power series, [`ModPForms.thetaPS`](def/CuspForm_ModPForms.html#L17) sends $\varphi$ to the power series whose $n$-th coefficient is $n \cdot a_n$, where $a_n$ is the $n$-th coefficient of $\varphi$ and $n$ is the image of the natural number $n$ in $K$. On Laurent series (Hahn series over $\mathbb{Z}$ with coefficients in $K$), [`ModularCurve.thetaL`](def/ModularCurve_QExpansionDiff.html#L16) is the $K$-linear endomorphism sending $f$ to $\mathrm{single}(1,1) \cdot f'$, that is, the formal derivative of $f$ multiplied by the monomial $q$. The assertion is that these agree under the canonical ring embedding $\mathrm{ofPowerSeries}\colon K[[q]] \to K((q))$: the image of $\mathrm{thetaPS}(\varphi)$ in $K((q))$ equals $\mathrm{thetaL}$ applied to the image of $\varphi$. Equivalently, $\iota(\theta\varphi) = q \cdot \iota(\varphi)'$ in $K((q))$, both sides having $n$-th coefficient $n a_n$ for $n \geq 0$ and $0$ for $n < 0$.
--
--   This identifies the two incarnations of Ramanujan's operator $\theta = q\,d/dq$ used in the development: the one acting on $q$-expansions as power series, and the one acting on Laurent series on the differential/function-field side, where the $q$-expansion of a Kähler differential is obtained by applying $\theta$. It is used in the comparison of a differential $q$-expansion with $\mathrm{ofPowerSeries}$ of a scalar multiple of a power series, in [`ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero`](thm.html#ModularCurve.exists_eq_smul_of_diffQExpBar_eq_ofPowerSeries_smul_of_kaehlerH0_of_ratCurveModel_of_cuspSection_compat_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModPForms_ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries.lean

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModPForms.ofPowerSeries_thetaPS_eq_thetaL_ofPowerSeries
    (K : Type) [Field K] (φ : PowerSeries K) :
    HahnSeries.ofPowerSeries ℤ K (ModPForms.thetaPS φ) =
      ModularCurve.thetaL K (HahnSeries.ofPowerSeries ℤ K φ) := by sorry
