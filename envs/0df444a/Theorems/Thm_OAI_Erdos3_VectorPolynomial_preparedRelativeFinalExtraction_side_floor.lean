-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeFinalExtraction_side_floor
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeFinalExtraction_side_floor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T00:14:57.521793+00:00
-- url     : https://prove2.me/theorems/cadfd75a-ca59-4a4c-9d90-d43df15cc48b
-- title:
--   Side lengths above exp((p+2)^passagePower) are above exp of any smaller extraction
-- statement:
--   Let $X$ be a type, $N : X \to \mathbb{N}$, $p$ and $\mathrm{extraction}$ real numbers, and $C, \mathrm{passagePower}$ natural numbers. Assume $0 \le p$, $C \le \mathrm{passagePower}$, $\mathrm{extraction} \le (p+2)^C$, and $\exp\bigl((p+2)^{\mathrm{passagePower}}\bigr) \le N_i$ for every $i \in X$. Then $\mathrm{extraction} \le (p+2)^{\mathrm{passagePower}}$, and $e^{\mathrm{extraction}} \le N_i$ for every $i \in X$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeFinalExtraction_side_floor` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B032` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean#L845

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B032

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
    
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    
    
    

namespace AllocatedExternalCandidateSamplerFamily


end AllocatedExternalCandidateSamplerFamily

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedRelativeFinalExtraction_side_floor
    {X : Type*} (N : X → ℕ) {p extraction : ℝ} {C passagePower : ℕ}
    (hp : 0 ≤ p) (hC : C ≤ passagePower)
    (hextraction : extraction ≤ (p + 2) ^ C)
    (hN : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) :
    extraction ≤ (p + 2) ^ passagePower ∧
      ∀ i, Real.exp extraction ≤ (N i : ℝ) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
