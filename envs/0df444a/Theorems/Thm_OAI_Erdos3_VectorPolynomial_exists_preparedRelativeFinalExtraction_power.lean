-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedRelativeFinalExtraction_power
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedRelativeFinalExtraction_power
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-16T02:27:22.815344+00:00
-- url     : https://prove2.me/theorems/ff03c1cd-03e1-4b65-a04b-3e7520976e87
-- title:
--   The prepared relative final extraction cost is bounded by a power of p + 2
-- statement:
--   Let $m, \mathrm{degree}, \mathrm{basePower}, \mathrm{inputPower}, \mathrm{preparationPower}, \mathrm{requiredPower}$ be natural numbers and $\mathrm{discount}$ a real. Then there is a natural number $\mathrm{passagePower} \ge 2$ such that for every real $p \ge 0$,
--   $$\mathrm{spatialPatchExtractionCost}\Bigl(\mathrm{recoveredKernelScalarBudget}\bigl(\mathrm{preparedFinalScalarBudget}(m, \mathrm{degree}, t)\bigr)\Bigr) \le (p+2)^{\mathrm{passagePower}},$$
--   where
--   $$t = \mathrm{preparedRelativeFinalEnvelope}(\dots, p) = 2 + (p+2)^{\mathrm{preparationPower}} + (p+2)^{\mathrm{requiredPower}} + \bigl((p+2)^{\mathrm{basePower}} + 2\bigr)^{\mathrm{inputPower}} + \lceil \mathrm{discount}^{-1} \rceil + (p+2)^{\mathrm{basePower}} + \mathrm{degree}\cdot p$$
--   (with $\lceil\cdot\rceil$ Mathlib's natural-number ceiling `Nat.ceil`, which is $0$ on nonpositive reals), `preparedFinalScalarBudget m degree t` $= 2048\,t^3 + (t+2)^{k+1} + 2t + 1 + \mathrm{degree}\cdot t$ with $k =$ `preparedIntegralBasisExponent m` (a natural number defined by OpenAI from $m$), `recoveredKernelScalarBudget B` $= 8(B+1)^2$, and `spatialPatchExtractionCost L` $= 20(L+1)^2$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedRelativeFinalExtraction_power` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1344` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean#L824

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1344

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure C) (law : C → FiniteProbabilityWeights Ω)
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))

include hweight

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Classical

variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (A : AllocatedExternalCandidateSamplerFamily B U b S hb o hR hσ N poly hm τ ξ stride cells)

namespace AllocatedExternalCandidateSamplerFamily

variable [MeasurableSpace A.Path] [MeasurableSingletonClass A.Path]

end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedRelativeFinalExtraction_power
    (m degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) :
    ∃ passagePower : ℕ, 2 ≤ passagePower ∧ ∀ p : ℝ, 0 ≤ p →
      let t := preparedRelativeFinalEnvelope degree basePower inputPower
        preparationPower requiredPower discount p
      spatialPatchExtractionCost (recoveredKernelScalarBudget
        (preparedFinalScalarBudget m degree t)) ≤ (p + 2) ^ passagePower := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
