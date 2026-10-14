-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedPhysicalSourceMean_residue_comparison
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalSourceMean_residue_comparison
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-11T22:03:11.260379+00:00
-- url     : https://prove2.me/theorems/d2679eea-53e8-45ee-841d-16fdb50ef790
-- title:
--   The sliced physical source mean of a Lipschitz test is close to its residue mean
-- statement:
--   All data are section variables. Fix a natural number $m$; finite types $G$, $X$, $T$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$, $\sigma_j > 0$; a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); and types $E_j$. Let short be the predicate `allocatedShortAxis U basis S.value`, Active the non-short axes, degree $=$ `layerSamplerDegree I n`, Input $= \Sigma_{a \in \mathrm{Active}}\, B_a \times \mathrm{Fin}(\mathrm{degree}(a))$, FullInput $=$ `PrincipalTupleIndex B degree`, Out $=$ `Sigma (AllocatedCongruenceRankOutput X E short)`, and budget $=$ `allocatedPhysicalRootBudget B U basis S (fun _ => 0)`.
--
--   Further fix: $\mathrm{HP}, \mathrm{stepP} : \mathrm{FullInput} \to \mathbb N$ and $\mathrm{cP} : \mathrm{FullInput} \to \mathbb Z$ with $0 \le \mathrm{cP}_j + \mathrm{stepP}_j v < $ `allocatedPrincipalSides B U basis S j` for all $v < \mathrm{HP}_j$ (hinsideP) and $\mathrm{HP}_j > 0$ (hHP); reals $\tau > 0$ (hτ) and $\xi > 0$ (hξ); $\mathrm{box} : X \to \mathbb N$ with positive values (hbox); $\mathrm{integerFrame} : \mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X \to \mathbb Z$ in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths budget τ ξ box) 1` (hframe); $\mathrm{HG} : G \to \mathbb N$ with $\mathrm{HG}_g \ge 2$ (hHG), $\mathrm{cG} : G \to \mathbb Z$, $\mathrm{stepG} \in \mathbb N$ with $\mathrm{stepG} > 0$ (hstepG), each progression `integerProgressionSupport (cG g) stepG (HG g)` $= \{\mathrm{cG}_g + \mathrm{stepG}\cdot k : 0 \le k < \mathrm{HG}_g\}$ contained in $[0, S.\mathrm{value})$ (hcontainedG); an equivalence $e : G \simeq X \oplus (X \oplus T)$ with the matrices `fixedSpatialKernelBlock e budget S.value (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) b` of nonzero determinant for $b = \mathrm{false}$ (h0) and $b = \mathrm{true}$ (h1); $|B_a| \ge 4$ for every active axis $a$ (hB), and a chosen element $b_a \in B_a$ for every active $a$; a sample in `CoefficientSamplerArrays I n` over `LayerSamplerVariables G I n B` that is `mixedArraySupported` for `allocatedLayerCenters`, `allocatedLayerWidths` and `allocatedLayerIntegerPMFs B U basis hR hσ S` in every layer $j$ (hs); a real $t > 0$ (ht) with $|\sigma_j| \le t$ (hσbound); $H : \mathrm{Input} \to \mathbb N$ with $H_j \ge 2$ (hH) and $c : \mathrm{Input} \to \mathbb Z$; a real $\delta$ with $0 < \delta \le 1$ (hδ, hδone) such that each `integerProgressionSupport (c j) stepG (H j)` lies in $[0, S.\mathrm{value})$ (hsubset) and has at least $\delta\, S.\mathrm{value}$ elements (hdense); a natural number $q \ne 0$ with $q \le \mathrm{HG}_g$ and $K q/\mathrm{HG}_g < 1$ for all $g$ (hsizeG, hsmallG), and $q \le H_j$ and $K q/H_j < 1$ for all $j$ (hsize, hsmall), where $K = $ `scalarCubeGridBoundaryConstant Empty`; a real $\varepsilon \ge 0$ (hε) with $\mathrm{stepG}/S.\mathrm{value} \le \varepsilon$, required for each index of Input (hmesh); a real $\eta > 0$ (hη); $A \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $A$-Lipschitz (hA) and the tail condition (htail) $|t|\cdot$ `polynomialMassC2Budget` $(|\mathrm{Input}|, m, 1) \le$ `slicedPrincipalC2Tolerance` $(|\mathrm{Input}|, |\mathrm{Active}|, m, 1,$ `unitProfilePrincipalLowerBound B`$, \delta/2, A, \eta)$; a type Cidx and a map $\mathrm{selected} : \mathrm{Cidx} \to \Sigma_j\, \mathrm{Fin}(n_j)$; $\mathrm{base} : X \to \mathbb Z$; $\mathrm{deck}_j :$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` $\to E_j \to \mathbb Z$; $\mathrm{projection}_j : $ `AllocatedDegreeActiveAxis short j` $\to$ `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` $\to \mathbb Z$; and a test function $\mathrm{test}(\mathrm{grid}, \mathrm{residue}, y) \in \mathbb C$, where $\mathrm{grid} : \mathrm{Cidx} \to (\text{the finsets of Empty}) \to \mathbb Z$, $\mathrm{residue} : \mathrm{Out} \to \mathbb Z/q$, and $y \in \mathbb R^{\Sigma_{x \in X} (\mathrm{Unit} \oplus \mathrm{Empty})} \times \mathbb R^{\Sigma_{a \in \mathrm{Active}} \mathrm{Unit}}$, which for each grid and residue is $K_\varphi$-Lipschitz in $y$ for some $K_\varphi \in \mathbb R_{\ge 0}$ (htest) and satisfies $\|\mathrm{test}(\mathrm{grid}, \mathrm{residue}, y)\| \le 1$ (hbound).
--
--   Let actualDensity $=$ `allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c`. Then
--   $$\|\mathrm{sourceMean} - \mathrm{finiteReference}\| \le \mathrm{comparisonError},$$
--   where sourceMean $=$ `allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base deck projection test` (a complex average of the test over the inactive affine interval law, the scalar-cube kernels on $G$ and on the active inputs, and the embedded physical sites), finiteReference $=$ `allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected base deck projection test actualDensity` (the same average with uniform residues mod $q$ in place of the kernels and integration of the test against actualDensity), and comparisonError $=$ `allocatedSlicedPhysicalComparisonError B U basis S ξ HG H q` with parameters $t, \varepsilon, \eta, K_\varphi$ (an explicit real combination of $\sum_j q/H_j$, $\sum_g q/\mathrm{HG}_g$, $\varepsilon$, $\eta$ and $\xi$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalSourceMean_residue_comparison` in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B179`, `OAIErdos3B180`, `OAIErdos3B183` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean#L269

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B179
import Definitions.Def_OAIErdos3B180
import Definitions.Def_OAIErdos3B183

namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a}

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X T : Type*} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Output" => (Σ _a : Active, Unit)

local notation "Spatial" => ((Σ _ : X, Unit ⊕ Empty) → ℝ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
variable (HP stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (cP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinsideP : ∀ j (v : Fin (HP j)), 0 ≤ cP j + (stepP j : ℤ) * v.val ∧
  cP j + (stepP j : ℤ) * v.val < allocatedPrincipalSides B U basis S j)
variable (hHP : ∀ j, 0 < HP j)

variable (τ ξ : ℝ)
variable (hτ : 0 < τ)
variable (hξ : 0 < ξ)
variable (box : X → ℕ)
variable (hbox : ∀ x, 0 < box x)
variable (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1)
variable (HG : G → ℕ)
variable (hHG : ∀ g, 2 ≤ HG g)
variable (cG : G → ℤ)
variable (stepG : ℕ)
variable (hstepG : 0 < stepG)
variable (hcontainedG : ∀ g, integerProgressionSupport (cG g) (stepG : ℤ) (HG g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (e : G ≃ X ⊕ (X ⊕ T))
variable (h0 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false).det ≠ 0)
variable (h1 : (fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) (S.value : ℝ) (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) true).det ≠ 0)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, 4 ≤ Fintype.card (B a.val))
variable (sample : (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n))
variable (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
variable {t : ℝ}
variable (ht : 0 < t)
variable (hσbound : ∀ j, |σ j| ≤ t)
variable (H : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℕ)
variable (c : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)) → ℤ)
variable (hH : ∀ j, 2 ≤ H j)
variable {δ : ℝ}
variable (hδ : 0 < δ)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (stepG : ℤ) (H j) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
variable (hdense : ∀ j, δ * S.value ≤
      ((integerProgressionSupport (c j) (stepG : ℤ) (H j)).card : ℝ))
variable (q : ℕ)
variable [NeZero q]
variable (hsizeG : ∀ g, q ≤ HG g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / HG g) < 1)
variable (hsize : ∀ j, q ≤ H j)
variable (hsmall : ∀ j, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / H j) < 1)
variable {ε : ℝ}
variable (hε : 0 ≤ ε)
variable (hmesh : ∀ _j : (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val)), (stepG : ℝ) / S.value ≤ ε)
variable (hδone : δ ≤ 1)
variable (b : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val)
variable {η : ℝ}
variable (hη : 0 < η)
variable (A : ℝ≥0)
variable (hA : LipschitzWith A Real.smoothTransition)
variable (htail : |t| * polynomialMassC2Budget (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, B a.val × Fin (layerSamplerDegree I n a.val))) (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}) m 1
        (unitProfilePrincipalLowerBound B) (δ / 2) A η)
variable {Cidx : Type*}
variable (selected : Cidx → Σ j : Fin m, Fin (n j))
variable (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis (allocatedShortAxis (I := I) U basis S.value) j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ}
variable (hV : gridVolume ≠ 0)
variable (test : (Cidx → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod q) → (((Σ _ : X, Unit ⊕ Empty) → ℝ) × ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℂ)
variable {Kφ : ℝ≥0}
variable (htest : ∀ grid residue, LipschitzWith Kφ (test grid residue))
variable (hbound : ∀ grid residue y, ‖test grid residue y‖ ≤ 1)

local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base deck projection test
local notation "finiteReference" => allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP
  integerFrame cG stepG sample c q selected base deck projection test actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Kφ)

omit [∀ j, Fintype (E j)] in
include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail htest hbound hτ hξ hbox hframe in
theorem allocatedSlicedPhysicalSourceMean_residue_comparison :
    ‖sourceMean - finiteReference‖ ≤ comparisonError := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
