-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeEndpointMinimumScale_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumScale_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T01:51:39.133048+00:00
-- url     : https://prove2.me/theorems/9b331a50-b7c7-4ed2-a53c-d01b1f77b4f2
-- title:
--   The relative-endpoint minimum scale dominates every floor it is built from
-- statement:
--   Let $\mathrm{seed} \ge 0$ and $\mathrm{periodLog}, \mathrm{childLog}, \mathrm{cost}, \mathrm{comparisonLog}$ be real numbers. Put $E = \max(0, \mathrm{periodLog}, \mathrm{childLog}, \mathrm{cost}+1, \mathrm{comparisonLog})$ (`preparedSlicedForecastCommonFloorExponent`), $F = \lceil e^{E} \rceil$ (`preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog`), $L_{\min} = $ `preparedRelativeEndpointMinimumScale seed periodLog childLog cost comparisonLog` $= \max(\lceil e^{\mathrm{seed}} \rceil, F)$ (a natural number) and $P_{\min} = $ `preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog` $= \max(\mathrm{seed}+1, E+1)$; ceilings are natural-number ceilings. Then: $0 \le P_{\min}$; $1 \le L_{\min}$; $L_{\min} \le e^{P_{\min}}$; $\lceil e^{\mathrm{seed}} \rceil \le L_{\min}$; $F \le L_{\min}$; `preparedSlicedForecastChildSize childLog` $= \lceil e^{\mathrm{childLog}} \rceil \le L_{\min}$; $2e^{\mathrm{cost}} \le L_{\min}$; every natural number $T$ with $T \le e^{\mathrm{periodLog}}$ satisfies $T \le L_{\min}$; and every natural number $L$ with $L \le e^{\mathrm{comparisonLog}}$ satisfies $L \le L_{\min}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumScale_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointSourceBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1327` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeEndpointSourceBounds.lean#L188

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1327

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeEndpointMinimumScale_bounds
    {seed : ℝ} (hseed : 0 ≤ seed) (periodLog childLog cost comparisonLog : ℝ) :
    let Lmin := preparedRelativeEndpointMinimumScale seed periodLog childLog cost comparisonLog
    let Pmin := preparedRelativeEndpointMinimumLog seed periodLog childLog cost comparisonLog
    0 ≤ Pmin ∧ 1 ≤ Lmin ∧ (Lmin : ℝ) ≤ Real.exp Pmin ∧
      ⌈Real.exp seed⌉₊ ≤ Lmin ∧
      preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog ≤ Lmin ∧
      preparedSlicedForecastChildSize childLog ≤ Lmin ∧
      2 * Real.exp cost ≤ (Lmin : ℝ) ∧
      (∀ T : ℕ, (T : ℝ) ≤ Real.exp periodLog → T ≤ Lmin) ∧
      (∀ Lcompare : ℕ, (Lcompare : ℝ) ≤ Real.exp comparisonLog → Lcompare ≤ Lmin) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
