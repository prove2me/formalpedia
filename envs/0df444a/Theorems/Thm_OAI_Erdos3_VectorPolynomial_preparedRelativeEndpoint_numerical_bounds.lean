-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpoint_numerical_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_numerical_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:55:14.291562+00:00
-- url     : https://prove2.me/theorems/7bdcf610-fc78-44cf-ad66-41665b2dfbf8
-- title:
--   Inputs bounded by the relative-endpoint base give the endpoint logs within T and K
-- statement:
--   Let $m,\mathrm{earlyPower},M,n_X,J_{\mathrm{alloc}}$ be natural numbers and $B,P_{\dim},\mathrm{cost},p_{\mathrm{Radius}},\mathrm{gainLog},Q_{\mathrm{stride}},P_{\mathrm{chart}},P_F,\mathrm{childCost},u,p,\mathrm{budget},\mathrm{seed}$ real numbers, with $B\ge 0$. Write $a$ for `preparedRelativeEndpointInputBase earlyPower B` (the real number $(B+2)^{\mathrm{earlyPower}}+B+1$) and $D$ for `allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc)` (cast to $\mathbb{R}$). Assume $D\le a$, $n_X+mM\le a$, that each of $P_{\dim},\mathrm{cost},p_{\mathrm{Radius}},\mathrm{gainLog},Q_{\mathrm{stride}},P_{\mathrm{chart}},P_F,\mathrm{childCost},u,p,\mathrm{budget}$ lies in $[0,a]$, and that $\mathrm{seed}\le a$. Set $t$ = `preparedRelativeEndpointInputScale m earlyPower B`, $T$ = `preparedRelativeEndpointGeometryScale m t` and $K$ = `preparedRelativeEndpointUniformKnob m t` (explicit real numbers built from $t$ by OpenAI). Set $E_{\mathrm{early}}=2u+4p+12$; let $\mathrm{nativeEarly}$ and $\mathrm{massEarly}$ be `preparedConcreteSlicedForecastNativeLog m M nX Jalloc Pdim cost pRadius gainLog Qstride PF Pchart childCost Eearly` and `preparedConcreteSlicedForecastMassLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart childCost Eearly`; $P_{\mathrm{test}}$ = `preparedRelativeEndpointTestLog budget nativeEarly` (that is, $\max(\mathrm{budget},3\,\mathrm{nativeEarly}+3)$); $E_{\mathrm{compare}}$ = `preparedRelativeEndpointComparisonLog budget nativeEarly massEarly u p cost`; $\mathrm{nativeLate}$ and $\mathrm{massLate}$ the same two native and mass logs with $E_{\mathrm{early}}$ replaced by $E_{\mathrm{compare}}+8$; $P_{\mathrm{spatial}}$ = `preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost`; with $e$ = `nativeForecastAmbientExponent m` (a natural number chosen by OpenAI from an existence statement),
--   $$\mathrm{nativeAmbient}=\big(\max(\max(P_{\mathrm{spatial}},\,2\max(P_{\mathrm{test}},3\,\mathrm{nativeLate}+3)+1),\ \mathrm{massLate}+E_{\mathrm{compare}}+8)+e\big)^{e};$$
--   $\mathrm{modelRequired}$ = `actualForecastDataModelRequired budget nativeEarly massEarly u p`; and $\mathrm{floorLog}=(T+10)^{2m+20}$. Then: $1\le T$, $t\le T$, $T\le K$, $1\le K$; each of $P_{\mathrm{test}},E_{\mathrm{compare}},\mathrm{nativeEarly},\mathrm{massEarly},\mathrm{nativeLate},\mathrm{massLate},\mathrm{modelRequired},\mathrm{nativeAmbient}$ lies in $[0,T]$; and each of `preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog`, `preparedRelativeEndpointGoodLog Ptest` ($=2P_{\mathrm{test}}+1$), `preparedRelativeEndpointSigmaLog D preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m`, `preparedRelativeEndpointCoarseLog D preparedSlicedForecastPrimitiveCap Ptest Ecompare`, `preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog` ($=\max(\mathrm{modelRequired},\mathrm{nativeAmbient},\mathrm{floorLog})$) and $\mathrm{floorLog}$ is at most $K$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpoint_numerical_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointNumericalBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1346` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointNumericalBounds.lean#L235

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1346

namespace OAI

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

 theorem preparedRelativeEndpoint_numerical_bounds
    (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost u p budget seed : ℝ}
    (hB : 0 ≤ B)
    (hDbase : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hDmod : ((nX + m * M : ℕ) : ℝ) ≤ preparedRelativeEndpointInputBase earlyPower B)
    (hPdim : Pdim ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hcost : cost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hRadius : pRadius ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hGain : gainLog ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hStride : Qstride ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChart : Pchart ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hPF : PF ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hu : u ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hp : p ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hbudget : budget ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B))
    (hseed : seed ≤ preparedRelativeEndpointInputBase earlyPower B) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    let T := preparedRelativeEndpointGeometryScale m t
    let K := preparedRelativeEndpointUniformKnob m t
    let Eearly := 2 * u + 4 * p + 12
    let nativeEarly := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost Eearly
    let massEarly := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost Eearly
    let Ptest := preparedRelativeEndpointTestLog budget nativeEarly
    let Ecompare := preparedRelativeEndpointComparisonLog budget nativeEarly massEarly u p cost
    let nativeLate := preparedConcreteSlicedForecastNativeLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride PF Pchart childCost (Ecompare + 8)
    let massLate := preparedConcreteSlicedForecastMassLog m M nX Jalloc
      Pdim cost pRadius gainLog Qstride Pchart childCost (Ecompare + 8)
    let Pspatial := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
    let nativeAmbient := (max (max Pspatial (2 * max Ptest (3 * nativeLate + 3) + 1))
      (massLate + Ecompare + 8) + nativeForecastAmbientExponent m) ^ nativeForecastAmbientExponent m
    let modelRequired := actualForecastDataModelRequired budget nativeEarly massEarly u p
    let floorLog := (T + 10) ^ (2 * m + 20)
    1 ≤ T ∧ t ≤ T ∧ T ≤ K ∧ 1 ≤ K ∧
    Ptest ∈ Set.Icc 0 T ∧ Ecompare ∈ Set.Icc 0 T ∧
    nativeEarly ∈ Set.Icc 0 T ∧ massEarly ∈ Set.Icc 0 T ∧
    nativeLate ∈ Set.Icc 0 T ∧ massLate ∈ Set.Icc 0 T ∧
    modelRequired ∈ Set.Icc 0 T ∧ nativeAmbient ∈ Set.Icc 0 T ∧
    preparedRelativeEndpointMinimumLog seed 0 childCost cost floorLog ≤ K ∧
    preparedRelativeEndpointGoodLog Ptest ≤ K ∧
    preparedRelativeEndpointSigmaLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare cost m ≤ K ∧
    preparedRelativeEndpointCoarseLog
      (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ))
      preparedSlicedForecastPrimitiveCap Ptest Ecompare ≤ K ∧
    preparedRelativeEndpointAmbientLog modelRequired nativeAmbient floorLog ≤ K ∧ floorLog ≤ K := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
