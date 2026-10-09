-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedRelativeFinalEnvelope_ready_requirements
-- name    : OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_ready_requirements
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T09:39:58.959569+00:00
-- url     : https://prove2.me/theorems/8db5106f-1136-4bb3-a433-76ba140e5c7a
-- title:
--   The prepared final scalar budget dominates the ready requirements
-- statement:
--   Let $m$, `degree`, $D$, $D_{\mathrm{mod}}$, `cardVars`, $b$ (`basePower`), $e$ (`inputPower`), $\pi$ (`preparationPower`) and $\rho$ (`requiredPower`) be natural numbers, and let `discount`, $p$, $K$, `childCost`, $P$ (`preparationP`), `qcap`, `qnative` and `cost` be real numbers. Write $E_{\mathrm{deg}}$ for the natural number chosen (`Classical.choose`) from OpenAI's existence theorem `exists_relative_finite_returned_fiber_normalization degree` (at universe levels $0,0$). Assume $0\le p$; $K\le((p+2)^b+2)^e$; $D\le p$; $D_{\mathrm{mod}}\le K$; $\mathrm{childCost}\le(p+2)^b$; $0\le P\le\max\big((p+2)^b,(p+2)^\pi,(p+2)^\rho+1\big)$; $(\mathrm{childCost}+\mathrm{cardVars}+4)^{E_{\mathrm{deg}}}\le(p+2)^b$; and `qcap`, `qnative`, `cost` are each at most $K$. Let $t=$ `preparedRelativeFinalEnvelope degree b e π ρ discount p` $=2+(p+2)^\pi+(p+2)^\rho+((p+2)^b+2)^e+\lceil\mathrm{discount}^{-1}\rceil+(p+2)^b+\mathrm{degree}\cdot p$ (natural-number ceiling), let $\mathrm{crt}=\max(1,\mathrm{discount}^{-1},K)$, and let $\beta=$ `preparedFinalScalarBudget m degree t` $=2048t^3+(t+2)^{k+1}+2t+1+\mathrm{degree}\cdot t$, where $k=$ `preparedIntegralBasisExponent m` (a natural number depending on $m$). Then: $1\le\beta$; $\mathrm{childCost}+\mathrm{degree}\cdot D\le\beta$; $D_{\mathrm{mod}}\le\beta$; $2048\,\mathrm{crt}^3+(P+2)^{k+1}\le\beta$; $2(\mathrm{childCost}+\mathrm{cardVars}+4)^{E_{\mathrm{deg}}}+1\le\beta$; and `qcap`, `qnative`, `cost` are each at most $\beta$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedRelativeFinalEnvelope_ready_requirements` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B130` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedRelativeFinalPower.lean#L787

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130

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

theorem preparedRelativeFinalEnvelope_ready_requirements
    (m degree D Dmod cardVars basePower inputPower preparationPower requiredPower : ℕ)
    (discount : ℝ) {p K childCost preparationP qcap qnative cost : ℝ}
    (hp : 0 ≤ p) (hK : K ≤ ((p + 2) ^ basePower + 2) ^ inputPower)
    (hD : (D : ℝ) ≤ p) (hDmod : (Dmod : ℝ) ≤ K)
    (hchild : childCost ≤ (p + 2) ^ basePower)
    (hPrepzero : 0 ≤ preparationP)
    (hPrep : preparationP ≤ max ((p + 2) ^ basePower)
      (max ((p + 2) ^ preparationPower) ((p + 2) ^ requiredPower + 1)))
    (hNorm : (((childCost + (cardVars : ℝ) + 2) + 2) ^
      (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) ≤
        (p + 2) ^ basePower)
    (hcap : qcap ≤ K) (hnative : qnative ≤ K) (hcost : cost ≤ K) :
    let t := preparedRelativeFinalEnvelope degree basePower inputPower
      preparationPower requiredPower discount p
    let crtBudget := max 1 (max discount⁻¹ K)
    let budget := preparedFinalScalarBudget m degree t
    1 ≤ budget ∧
      childCost + (degree : ℝ) * D ≤ budget ∧
      (Dmod : ℝ) ≤ budget ∧
      2048 * crtBudget ^ 3 +
        (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget ∧
      2 * (((childCost + (cardVars : ℝ) + 2) + 2) ^
        (exists_relative_finite_returned_fiber_normalization.{0,0} degree).choose) + 1 ≤ budget ∧
      qcap ≤ budget ∧ qnative ≤ budget ∧ cost ≤ budget := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
