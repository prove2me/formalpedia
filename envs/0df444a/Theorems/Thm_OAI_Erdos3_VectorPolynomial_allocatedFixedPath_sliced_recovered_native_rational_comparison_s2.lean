-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_recovered_native_rational_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:44:28.364366+00:00
-- url     : https://prove2.me/theorems/ef926a02-beea-43a7-86af-27aba7eefbf0
-- title:
--   The sliced native evaluation mean along a fixed path is within the sliced physical comparison error of the rational reference mean
-- statement:
--   All named objects below are defined by OpenAI. Throughout, write $\mathcal{A}$ for the set of axes $a$ of `LayerSamplerAxis I n` that are not short (`¬allocatedShortAxis U basis S.value a`) and $\mathcal{J} = \Sigma_{a \in \mathcal{A}}\, B_a \times \mathrm{Fin}(\deg a)$, where $\deg a = $ `layerSamplerDegree I n a` $= a.1 + 1$.
--
--   **Data and hypotheses.**
--   - $m$ is a natural number with $m > 0$; $G, X, T$ are finite types; $I_j$ ($j<m$) finite types, $n : \mathrm{Fin}(m) \to \mathbb{N}$, $B_a$ finite types indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$; $J_j$ finite types; $U_j \subseteq \mathbb{R}^{J_j}$ subspaces; `basis j` a basis (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is the projected integer lattice (`hb`); $R_j > 0$, $\sigma_j > 0$; `S : LayerSamplerScale B U basis R σ`; $E_j$ finite types.
--   - `PrimeIndex` is a finite type, `primes, exponent : PrimeIndex → ℕ` with every `primes l` a nonzero prime, and the prime powers $\mathrm{primes}_l^{\mathrm{exponent}_l}$ pairwise coprime.
--   - `HP, stepP : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ` and `cP` into $\mathbb{Z}$ with $HP_j > 0$ and $0 \le cP_j + stepP_j\, v < $ `allocatedPrincipalSides B U basis S j` for every $v < HP_j$.
--   - $\tau > 0$, $\xi > 0$; `box : X → ℕ` with all values positive; `integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ` lying in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1`.
--   - `HG : G → ℕ` with $HG_g \ge 2$, `cG : G → ℤ`, `stepG` $> 0$, and every progression $\{cG_g + \mathrm{stepG}\cdot k : k < HG_g\}$ (`integerProgressionSupport`) is contained in $[0, \texttt{S.value})$.
--   - $e : G \simeq X \sqcup (X \sqcup T)$, and the two blocks `fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) S.value (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false` and `… true` have nonzero determinant.
--   - $|B_a| \ge 4$ for every $a \in \mathcal{A}$.
--   - `sample : CoefficientSamplerArrays I n` (over the variables `LayerSamplerVariables G I n B`) with, for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)`.
--   - $t > 0$ with $|\sigma_j| \le t$ for every $j$.
--   - `H : 𝒥 → ℕ`, `c : 𝒥 → ℤ` with $H_j \ge 2$; $\delta$ with $0 < \delta \le 1$; for every $j \in \mathcal{J}$, the progression $\{c_j + \mathrm{stepG}\cdot k : k < H_j\}$ is contained in $[0, \texttt{S.value})$ and has at least $\delta\cdot\texttt{S.value}$ elements.
--   - $q \ge 1$ is a natural number with $q \le HG_g$ and $\texttt{scalarCubeGridBoundaryConstant Empty}\cdot (q / HG_g) < 1$ for all $g$, and $q \le H_j$ and $\texttt{scalarCubeGridBoundaryConstant Empty}\cdot(q/H_j) < 1$ for all $j \in \mathcal{J}$.
--   - $\varepsilon \ge 0$ with $\mathrm{stepG}/\texttt{S.value} \le \varepsilon$ (stated for each $j \in \mathcal{J}$).
--   - `b` chooses an element $b_a \in B_a$ for every $a \in \mathcal{A}$.
--   - $\eta > 0$; $A \in \mathbb{R}_{\ge 0}$ is a Lipschitz constant of `Real.smoothTransition`; and
--   $$|t| \cdot \texttt{polynomialMassC2Budget}\ |\mathcal{J}|\ m\ 1 \le \texttt{slicedPrincipalC2Tolerance}\ |\mathcal{J}|\ |\mathcal{A}|\ m\ 1\ (\texttt{unitProfilePrincipalLowerBound}\ B)\ (\delta/2)\ A\ \eta.$$
--   - $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$; `bW j` $\mathbb{Z}$-bases (indexed by $E_j$) of the lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)`.
--   - `W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` with `W.modulus` and `W.cover` both dividing $q$.
--   - `xref : G → IntegerScalarCubeBox Empty S.value`, `base : X → ℤ`, `read : AllocatedActualCoefficientIndex G X I E n B → ℤ`.
--   - $q$ divides $N_{\mathrm{crt}} = \prod_l \mathrm{primes}_l^{\mathrm{exponent}_l}$; `gridVolume` is a nonzero real.
--   - `nativePoly j : VectorPolynomial X ℝ (J j → ℝ)` with all coefficients in $U_j$ and degree at most $j+1$ for the unit weight on $X$.
--   - (`hbase`) `canonicalCoefficientSample U basis hb o sample` equals `affineSampleCoefficientTorus U nativePoly hmem` evaluated at the real point $(k, x) \mapsto (\texttt{integerBaseTranslation base} + \texttt{integerFrame})(k, x)$.
--   - (`hsmallChart`) $|\texttt{coefficientSamplerAmbientPoint U basis o sample}\ a| < 1/2$ for every $a$.
--   - (`hread`) for every event on `CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover`, the chart event `coefficientDeckChartEvent U bW basis hb o W.cover event` holds for `affineCoefficientCoverSample U nativePoly hmem W.cover` (at the same real point) iff the event holds for `allocatedReadCoefficientChartResidues` of `read` reduced mod `W.cover`.
--
--   **Statement.** Let `nativeTest` = `W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover (fun a => base a / box a) τ`, $K_{\mathrm{native}} = \mathrm{Lip}\cdot\max(\|\tau/8\|_+, \texttt{forecastNativeAmbientLip U basis o R})$, `actualDensity` = `allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c`, `projection` = `allocatedOriginalSampleCongruenceProjection B U basis S sample`, and
--   `rationalReference` = `allocatedSlicedPhysicalRationalMean B U basis S primes exponent HP stepP cP hinsideP hHP integerFrame cG stepG sample c q (allocatedShortIntegerSelection U basis S.value) xref base (allocatedReadDeck read) projection hcoprime hqN nativeTest actualDensity` (with this `gridVolume`). Then
--   $$\bigl\|\texttt{allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset} - \texttt{rationalReference}\bigr\| \le \texttt{allocatedSlicedPhysicalComparisonError B U basis S}\ \xi\ HG\ H\ q,$$
--   where the error term is taken with parameters $t$, $\varepsilon$, $\eta$ and $K_\varphi = K_{\mathrm{native}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B254` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_recovered_native_rational_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B254

section

namespace OAI

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

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
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

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (hm : 0 < m) (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (xref : G → IntegerScalarCubeBox Empty S.value)
variable (base : X → ℤ)
variable (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hp : ∀ l, (primes l).Prime)
variable (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
variable (hqN : q ∣ (∏ l, primes l ^ exponent l))
variable {gridVolume : ℝ} (hV : gridVolume ≠ 0)

local notation "selected" => allocatedShortIntegerSelection U basis S.value
local notation "nativeTest" => W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover
  (fun a => (base a : ℝ) / box a) τ
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedNativeRecoveredCoverNeZero
variable (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j a, coefficients (nativePoly j) a ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (nativePoly j))
variable (hbase : canonicalCoefficientSample U basis hb o sample =
  affineSampleCoefficientTorus U nativePoly hmem
    (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
      integerFrame) (k, x) : ℝ)))
variable (hsmallChart : ∀ a, |coefficientSamplerAmbientPoint U basis o sample a| < 1 / 2)
variable (hread : ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover → Prop,
  coefficientDeckChartEvent U bW basis hb o W.cover event
    (affineCoefficientCoverSample U nativePoly hmem W.cover
      (fun k x => ((integerBaseTranslation (K := LayerSamplerVariables G I n B) base +
        integerFrame) (k, x) : ℝ))) ↔
    event (allocatedReadCoefficientChartResidues (fun i => (read i : ZMod W.cover))))

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe hmem hdegree hbase hsmallChart hread in

theorem allocatedFixedPath_sliced_recovered_native_rational_comparison_s2 :
    ‖allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset -
      rationalReference‖ ≤ comparisonError := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
