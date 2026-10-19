-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSample_slice_complex_perturbation_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:07:22.048291+00:00
-- url     : https://prove2.me/theorems/d6d0f5dc-b120-4fc3-b805-95d67a8bbdb1
-- title:
--   Replacing the lift map of an allocated original sample by its full slice map changes a bounded complex test average by at most 2η
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (with scale value `S.value`). Write short for `allocatedShortAxis U basis S.value`, Active for the set of axes $a$ that are not short, Input for the index type of triples $(a, \beta, i)$ with $a$ active, $\beta \in B_a$ and $i < $ `layerSamplerDegree I n a`, and Output for the index type of active axes (one coordinate per active axis). Let $x : G \to$ `IntegerScalarCubeBox Empty S.value`, $u$ an element of `PrincipalAxisTuples short (allocatedPrincipalSides B U basis S)` (with empty index type $\alpha$), and `lower`, `width` real-valued functions on Input.
--
--   Let `sample` be a `CoefficientSamplerArrays` value (over the variables `LayerSamplerVariables G I n B`), and assume:
--   - for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` holds (each real row of the $j$-th array has nonzero affine product profile density and each integer entry lies in the support of the corresponding PMF);
--   - $|\mathrm{lower}(a, p)| + |\mathrm{width}(a, p)| \le 1$ for all $a$ and $p$;
--   - $b$ assigns to each active axis $a$ an element $b(a) \in B_a$; $\delta, \eta$ are reals with $0 < \delta \le 1$ and $0 < \eta$; $\delta \le \mathrm{width}(a, (b(a), i))$ and $0 \le \mathrm{lower}(a, (b(a), i))$ for all $a, i$;
--   - $A$ is a nonnegative real such that `Real.smoothTransition` is $A$-Lipschitz;
--   - $t > 0$ is real with $|\sigma_j| \le t$ for all $j$, and
--   $$|t| \cdot \texttt{polynomialMassC2Budget}\ |\mathrm{Input}|\ m\ 1 \le \texttt{slicedPrincipalC2Tolerance}\ |\mathrm{Input}|\ |\mathrm{Active}|\ m\ 1\ (\texttt{unitProfilePrincipalLowerBound B})\ \delta\ A\ \eta,$$
--   where `polynomialMassC2Budget N d C` $= (1 + Nd)^2 C$, `unitProfilePrincipalLowerBound B` $= 1/\bigl(8(\sum_a |B_a| + 1)\bigr)$, and `slicedPrincipalC2Tolerance` is an explicit positive tolerance of OpenAI;
--   - $\varphi : \mathbb{R}^{\mathrm{Output}} \to \mathbb{C}$ is measurable with $|\varphi(z)| \le 1$ for all $z$.
--
--   Then, with $\mu$ = `unitBoxMeasure Input` (Lebesgue measure restricted to the unit box $(0,1]^{\mathrm{Input}}$),
--   $$\Bigl|\int \varphi\bigl(\texttt{allocatedOriginalSampleLiftMap B U basis S lower width sample}\ y\bigr)\,d\mu(y) - \int \varphi\bigl(\texttt{allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample}\ y\bigr)\,d\mu(y)\Bigr| \le 2\eta.$$
--   Here the lift map sends $y$ to the vector whose coordinate at an active axis is the sample's normalized constant coefficient divided by $R_j$ plus a sliced principal (degree-one) part built from the principal coefficients, `lower` and `width`; the full slice map evaluates the whole sample polynomial at OpenAI's slice substitution (built from $x$, $u$, `lower`, `width`) and divides by $R_j$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleFullSliceLipschitz.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleFullSliceLipschitz.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_slice_complex_perturbation)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

include hR hσ in
theorem allocatedOriginalSample_slice_complex_perturbation_s2
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (b : ∀ a : Active, B a.val)
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hw : ∀ a i, δ ≤ width a (b a, i))
    (hlower : ∀ a i, 0 ≤ lower a (b a, i))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {t : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
    (hsmall : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card Active) m 1
        (unitProfilePrincipalLowerBound B) δ A η)
    (φ : (Output → ℝ) → ℂ) (hφ : Measurable φ) (hbound : ∀ z, ‖φ z‖ ≤ 1) :
    ‖(∫ y, φ (allocatedOriginalSampleLiftMap B U basis S lower width sample y) ∂unitBoxMeasure Input) -
      ∫ y, φ (allocatedOriginalSampleFullSliceMap B U basis S x u lower width sample y)
        ∂unitBoxMeasure Input‖ ≤ 2 * η := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
