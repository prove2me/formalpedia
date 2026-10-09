-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeFinalEnvelope_bounds
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:25:33.689433+00:00
-- url     : https://prove2.me/theorems/153edd75-40e2-45c1-87e5-9e0c3fd2fc42
-- title:
--   The prepared relative final envelope dominates each of its ingredients
-- statement:
--   Let $\mathrm{degree}, \mathrm{basePower}, \mathrm{inputPower}, \mathrm{preparationPower}, \mathrm{requiredPower}$ be natural numbers and $\mathrm{discount}, p, K$ real numbers with $0 \le p$ and $K \le ((p+2)^{\mathrm{basePower}} + 2)^{\mathrm{inputPower}}$. Let $t = $ `preparedRelativeFinalEnvelope degree basePower inputPower preparationPower requiredPower discount p`, which OpenAI defines as
--   $$t = 2 + (p+2)^{\mathrm{preparationPower}} + (p+2)^{\mathrm{requiredPower}} + ((p+2)^{\mathrm{basePower}} + 2)^{\mathrm{inputPower}} + \lceil \mathrm{discount}^{-1} \rceil_{\mathbb{N}} + (p+2)^{\mathrm{basePower}} + \mathrm{degree}\cdot p,$$
--   with $\lceil\cdot\rceil_{\mathbb{N}}$ the natural-number ceiling (which is $0$ on nonpositive reals) and $0^{-1} = 0$. Then $1 \le t$; $\max\bigl((p+2)^{\mathrm{preparationPower}}, (p+2)^{\mathrm{requiredPower}} + 1\bigr) \le t$; $K \le t$; $\mathrm{discount}^{-1} \le t$; $(p+2)^{\mathrm{basePower}} \le t$; $\mathrm{degree}\cdot p \le t$; and $\max(1, \max(\mathrm{discount}^{-1}, K)) \le t$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_bounds` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B032` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean#L748

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

theorem preparedRelativeFinalEnvelope_bounds
    (degree basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K : ℝ} (hp : 0 ≤ p)
    (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    1 ≤ t ∧
      max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1) ≤ t ∧
      K ≤ t ∧ discount⁻¹ ≤ t ∧ (p + 2) ^ basePower ≤ t ∧
      (degree : ℝ) * p ≤ t ∧ max 1 (max discount⁻¹ K) ≤ t := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
