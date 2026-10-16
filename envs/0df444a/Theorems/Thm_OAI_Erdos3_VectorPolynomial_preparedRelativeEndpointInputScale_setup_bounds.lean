-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpointInputScale_setup_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale_setup_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:53:41.912922+00:00
-- url     : https://prove2.me/theorems/3c79f2ee-91e9-44d2-9384-80a0021bf205
-- title:
--   Inputs bounded by the relative-endpoint base give setup quantities in [0, t]
-- statement:
--   Let $m,\mathrm{earlyPower},M,n_X,J_{\mathrm{alloc}}$ be natural numbers and $B,P_{\dim},\mathrm{cost},p_{\mathrm{Radius}},\mathrm{gainLog},Q_{\mathrm{stride}},P_{\mathrm{chart}},P_F,\mathrm{childCost}$ real numbers, with $B\ge 0$. Write $a$ for `preparedRelativeEndpointInputBase earlyPower B` (the real number $(B+2)^{\mathrm{earlyPower}}+B+1$) and $D$ for `allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc)` (an explicit polynomial expression in $m$ and the natural number `enlargedPreparedCommonSamplerDimension m M Jalloc`, cast to $\mathbb{R}$). Assume $D\le a$, $n_X+mM\le a$, and that each of $P_{\dim},\mathrm{cost},p_{\mathrm{Radius}},\mathrm{gainLog},Q_{\mathrm{stride}},P_{\mathrm{chart}},P_F,\mathrm{childCost}$ lies in $[0,a]$. Let $t$ be `preparedRelativeEndpointInputScale m earlyPower B` (the real number $a+(a+e)^{e}+1$ with $e$ = `preparedRelativeEndpointPrimitiveExponent m`). Then each of the following lies in $[0,t]$: `preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost`, `preparedSlicedForecastBadLog m nX Qstride gainLog`, $\mathrm{cost}+1$, $\mathrm{gainLog}+n_X+8$, $p_{\mathrm{Radius}}$, $D$, the constant `preparedSlicedForecastPrimitiveCap`, $D+p_{\mathrm{Radius}}+1$, `preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart` (the real number $(n_X+m+mM)(p_{\mathrm{Radius}}+\mathrm{gainLog}+n_X+P_{\mathrm{chart}}+11)$), $P_F$ and $\mathrm{childCost}+1$; moreover $m\le t$, $n_X+mM\le t$ and $n_X\le t$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointInputScale_setup_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointNumericalBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1346` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointNumericalBounds.lean#L170

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

theorem preparedRelativeEndpointInputScale_setup_bounds (m earlyPower M nX Jalloc : ℕ)
    {B Pdim cost pRadius gainLog Qstride Pchart PF childCost : ℝ} (hB : 0 ≤ B)
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
    (hChild : childCost ∈ Set.Icc 0 (preparedRelativeEndpointInputBase earlyPower B)) :
    let t := preparedRelativeEndpointInputScale m earlyPower B
    preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ∈ Set.Icc 0 t ∧
    preparedSlicedForecastBadLog m nX Qstride gainLog ∈ Set.Icc 0 t ∧
    cost + 1 ∈ Set.Icc 0 t ∧ gainLog + nX + 8 ∈ Set.Icc 0 t ∧
    pRadius ∈ Set.Icc 0 t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ∈ Set.Icc 0 t ∧
    preparedSlicedForecastPrimitiveCap ∈ Set.Icc 0 t ∧
    (m : ℝ) ≤ t ∧ ((nX + m * M : ℕ) : ℝ) ≤ t ∧ (nX : ℝ) ≤ t ∧
    allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ∈ Set.Icc 0 t ∧
    preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ∈ Set.Icc 0 t ∧
    PF ∈ Set.Icc 0 t ∧ childCost + 1 ∈ Set.Icc 0 t := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
