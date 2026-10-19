-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:14:38.862376+00:00
-- url     : https://prove2.me/theorems/5c580549-dad0-4d6f-922d-9eb599408dcb
-- title:
--   The sliced physical residue mean equals the sliced physical rational (CRT) mean
-- statement:
--   Fix the data of OpenAI's allocated layer-sampler setup: a natural number $m$; finite types $G$, $X$, $T$, $I_j$, $J_j$, $E_j$ ($j < m$), $B(a)$ for each layer-sampler axis $a$, a finite index type $\mathrm{PrimeIndex}$ and an index type $C_{\mathrm{idx}}$; dimensions $n_j$; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases `basis j` (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$; reals $R_j > 0$, $\sigma_j > 0$; and a `LayerSamplerScale B U basis R σ` $S$. Write `short` = `allocatedShortAxis U basis S.value`, call the other axes active, and let $\mathrm{Input}$ be the set of triples (active axis $a$, element of $B(a)$, index below `layerSamplerDegree I n a`).
--
--   Let the following data be given:
--   - $\mathrm{primes}, \mathrm{exponent} : \mathrm{PrimeIndex} \to \mathbb{N}$ with every $\mathrm{primes}(l) \ne 0$, ($hp$) every $\mathrm{primes}(l)$ prime, and ($hcoprime$) the prime powers $\mathrm{primes}(l)^{\mathrm{exponent}(l)}$ pairwise coprime;
--   - $H_P, \mathrm{step}_P$ (natural-valued) and $c_P$ (integer-valued) on `PrincipalTupleIndex B (layerSamplerDegree I n)`, with $H_P > 0$ and $0 \le c_P(j) + \mathrm{step}_P(j)\, v < \texttt{allocatedPrincipalSides B U basis S}\ j$ for all $v < H_P(j)$;
--   - reals $\tau, \xi$; $\mathrm{box} : X \to \mathbb{N}$; an integer function `integerFrame` on $\texttt{Option}(\texttt{LayerSamplerVariables G I n B}) \times X$;
--   - $H_G : G \to \mathbb{N}$ with $H_G(g) \ge 2$; $c_G : G \to \mathbb{Z}$; $\mathrm{step}_G \in \mathbb{N}$ with $\mathrm{step}_G > 0$;
--   - an equivalence $e : G \simeq X \sqcup (X \sqcup T)$ such that ($h0$, $h1$) the two matrices `fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S 0) S.value (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) b` for $b$ = false and $b$ = true have nonzero determinant;
--   - ($hB$) $\lvert B(a)\rvert \ge 4$ for every active axis $a$;
--   - a `CoefficientSamplerArrays` value `sample` with ($hs$) `mixedArraySupported` on the layer centers, widths and integer PMFs `allocatedLayerCenters`, `allocatedLayerWidths`, `allocatedLayerIntegerPMFs` for every layer $j$;
--   - $H : \mathrm{Input} \to \mathbb{N}$ and $c : \mathrm{Input} \to \mathbb{Z}$;
--   - a natural number $q \ge 1$ with ($hqN$) $q$ dividing $\prod_l \mathrm{primes}(l)^{\mathrm{exponent}(l)}$;
--   - `selected` $: C_{\mathrm{idx}} \to \Sigma_{j<m}\{0,\dots,n_j-1\}$ with ($hshort$) $\texttt{basisAxisScale}(\texttt{basis}\ j_a, i_a) \le \texttt{S.value}^{\,j_a + 1}$ for every $a$, where $\texttt{selected}(a) = (j_a, i_a)$;
--   - $x_{\mathrm{ref}} : G \to$ `IntegerScalarCubeBox Empty S.value`; $\mathrm{base} : X \to \mathbb{Z}$; integer arrays `deck` and `projection` (indexed as in OpenAI's definitions);
--   - a real `gridVolume` with ($hV$) $\mathrm{gridVolume} \ne 0$;
--   - a complex-valued function `test` of a grid value (a map $C_{\mathrm{idx}} \to (\ldots \to \mathbb{Z})$), a residue vector in $(\mathbb{Z}/q)^{\mathrm{Out}}$ with $\mathrm{Out}$ = $\Sigma$ `AllocatedCongruenceRankOutput X E short`, and a real point.
--
--   (The hypotheses $hR$, $h\sigma$, $hs$, $hshort$, $hp$, $hV$ are included in the statement; no Lipschitz or boundedness hypothesis on `test` is assumed.)
--
--   Let `actualDensity` = `allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c` (a real density defined by OpenAI). Then
--   $$\texttt{allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected base deck projection test actualDensity}$$
--   equals
--   $$\texttt{allocatedSlicedPhysicalRationalMean B U basis S primes exponent HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection hcoprime hqN test actualDensity}$$
--   (with the given `gridVolume`). By OpenAI's definitions, the left side is the mean, over the short-axis tuple $u$ drawn from `allocatedInactiveAffineIntervalLaw … HP stepP cP` and over uniform residues $r_A \in (\mathbb{Z}/q)^{\mathrm{Input}}$, $r_G \in (\mathbb{Z}/q)^G$, of the integral against the measure with density `actualDensity` of `test` applied to the short grid `forecastInactiveShortGrid … u`, the joint residue output built from the residues $c_G(g) + \mathrm{step}_G r_G(g)$ and $c(j) + \mathrm{step}_G r_A(j)$, and the integration variable; the right side is the analogous sum over grid values of CRT-averaged rational inactive forecasts (`rationalInactiveForecast` with the CRT input law `crtPolynomialInputLaw`, divided by `gridVolume`) times the integral of `test` with residues reduced from $\mathbb{Z}/\prod_l \mathrm{primes}(l)^{\mathrm{exponent}(l)}$ to $\mathbb{Z}/q$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B247` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSlicedPhysicalResidueMean_eq_rationalMean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B247

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
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedPhysicalDensityCRTNeZero
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
local notation "finiteReference" => allocatedSlicedPhysicalResidueMean B U basis S HP stepP cP hinsideP hHP
  integerFrame cG stepG sample c q selected base deck projection test actualDensity
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection
  hcoprime hqN (gridVolume := gridVolume) test actualDensity

include hR hσ hs hshort hp hV in
theorem allocatedSlicedPhysicalResidueMean_eq_rationalMean_s2 :
    finiteReference = rationalReference := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
