-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_physical_rational_density_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:15:40.444984+00:00
-- url     : https://prove2.me/theorems/2ff29fa2-c3eb-4fb0-94e8-184710c07f68
-- title:
--   Along a fixed path, the sliced physical source mean is close to the rational reference mean against the sliced forecast density
-- statement:
--   All objects named in backticks are defined by OpenAI; the hypothesis names in parentheses are those of the Lean statement.
--
--   **Data.** Let $m$ be a natural number, $G, X, T$ finite types, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type $B_a$ to each axis $a$ of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$; the degree of $(j, \cdot)$ is $j+1$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $\mathrm{basis}_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$ (hR, hσ), and $S$ a `LayerSamplerScale B U basis R σ` (with positive natural number `S.value`). Let $E_j$ be finite types, $\mathrm{PrimeIndex}$ a finite type, and $\mathrm{primes}, \mathrm{exponent} : \mathrm{PrimeIndex} \to \mathbb{N}$ with $\mathrm{primes}(l) \neq 0$. Let $H_P, \mathrm{step}_P$ (natural numbers) and $c_P$ (integers) be functions on the triples `PrincipalTupleIndex B (layerSamplerDegree I n)` with $0 \le c_P(j) + \mathrm{step}_P(j)\, v < $ `allocatedPrincipalSides B U basis S j` for all $v < H_P(j)$ (hinsideP) and $H_P(j) > 0$ (hHP). A non-short axis is an axis that does not satisfy `allocatedShortAxis U basis S.value` (an axis $(j, \mathrm{inr}\ i)$ is short when $\lceil \|\mathrm{basis}_{j,i}\|^{-1} \rceil \le \texttt{S.value}^{j+1}$; axes $(j, \mathrm{inl}\ \cdot)$ are never short), and an active index is a triple $(a, \beta, k)$ with $a$ non-short, $\beta \in B_a$, $k \in \operatorname{Fin}(\deg a)$.
--
--   **Hypotheses.**
--   - $\tau > 0$, $\xi > 0$ (hτ, hξ); $\mathrm{box} : X \to \mathbb{N}$ with $\mathrm{box}(x) > 0$ (hbox); $\mathrm{integerFrame} : \operatorname{Option}(\texttt{LayerSamplerVariables G I n B}) \times X \to \mathbb{Z}$ lies in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box) 1` (hframe);
--   - $H_G : G \to \mathbb{N}$ with $H_G(g) \ge 2$ (hHG), $c_G : G \to \mathbb{Z}$, $\mathrm{step}_G > 0$ (hstepG), and each progression `integerProgressionSupport (cG g) stepG (HG g)` $= \{c_G(g) + \mathrm{step}_G\, i : 0 \le i < H_G(g)\}$ is contained in $[0, \texttt{S.value})$ (hcontainedG);
--   - $e : G \simeq X \sqcup (X \sqcup T)$, and the two $X \times X$ matrices `fixedSpatialKernelBlock e W₀ S.value F false` and `fixedSpatialKernelBlock e W₀ S.value F true` have nonzero determinant (h0, h1), where $W_0$ = `allocatedPhysicalRootBudget B U basis S (fun _ => 0)` and $F$ = `allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame`;
--   - $\#B_a \ge 4$ for every non-short axis $a$ (hB);
--   - `sample` is a `CoefficientSamplerArrays` element with `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for each $j$ (hs);
--   - $t > 0$ and $|\sigma_j| \le t$ for all $j$ (ht, hσbound);
--   - $H$ (natural numbers) and $c$ (integers) are functions on active indices with $H(j) \ge 2$ (hH), $\delta > 0$ (hδ), each progression `integerProgressionSupport (c j) stepG (H j)` contained in $[0, \texttt{S.value})$ (hsubset) and of cardinality at least $\delta \cdot \texttt{S.value}$ (hdense);
--   - $q$ is a positive natural number with $q \le H_G(g)$ and $c_0\, q / H_G(g) < 1$ for every $g$ (hsizeG, hsmallG), and $q \le H(j)$ and $c_0\, q/H(j) < 1$ for every active $j$ (hsize, hsmall), where $c_0$ = `scalarCubeGridBoundaryConstant Empty`;
--   - $\varepsilon \ge 0$ (hε); $\mathrm{step}_G/\texttt{S.value} \le \varepsilon$ (hmesh, stated once for each active index); $\delta \le 1$ (hδone);
--   - $b$ is a choice of an element $b(a) \in B_a$ for each non-short axis $a$ (so each such $B_a$ is nonempty);
--   - $\eta > 0$ (hη); $A \ge 0$ with Mathlib's `Real.smoothTransition` $A$-Lipschitz (hA);
--   - (htail) $|t| \cdot$ `polynomialMassC2Budget N₁ m 1` $\le$ `slicedPrincipalC2Tolerance N₁ N₂ m 1 (unitProfilePrincipalLowerBound B) (δ/2) A η`, with $N_1$ the number of active indices and $N_2$ the number of non-short axes;
--   - $\mathrm{selected} : C_{\mathrm{idx}} \to \Sigma_j \operatorname{Fin} n_j$ with `basisAxisScale (basis j) i` $\le \texttt{S.value}^{j+1}$ for every selected $(j, i)$ (hshort); $x_{\mathrm{ref}} : G \to$ `IntegerScalarCubeBox Empty S.value`; $\mathrm{base} : X \to \mathbb{Z}$; $\mathrm{deck}_j$ an integer function of a bounded coefficient exponent of degree $j+1$ and an element of $E_j$; $\mathrm{projection}_j$ an integer function of an active axis of degree $j$ and a bounded coefficient exponent;
--   - each $\mathrm{primes}(l)$ is prime (hp); the prime powers $\mathrm{primes}(l)^{\mathrm{exponent}(l)}$ are pairwise coprime (hcoprime); $q$ divides $\prod_l \mathrm{primes}(l)^{\mathrm{exponent}(l)}$ (hqN);
--   - $\mathrm{gridVolume} \neq 0$ (hV);
--   - `test` is a complex function of a grid ($C_{\mathrm{idx}} \to \{\emptyset\} \to \mathbb{Z}$), a residue (from `Σ AllocatedCongruenceRankOutput X E (allocatedShortAxis U basis S.value)` to $\mathbb{Z}/q$), and a real point $y$ (a pair of real functions on $X \times \mathrm{Unit}$ and on the non-short axes); for each grid and residue it is $K_\varphi$-Lipschitz in $y$ (htest, $K_\varphi \ge 0$) and bounded in norm by $1$ (hbound).
--
--   **Conclusion.** Let `actualDensity` = `allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c` (OpenAI's sliced forecast density), `sourceMean` = `allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base deck projection test` (the iterated mean, over the inactive affine interval law and the uniform cube laws on the kernel and active progressions, of `test` at the induced grid, residues modulo $q$, and normalized physical site values), and `rationalReference` = `allocatedSlicedPhysicalRationalMean B U basis S primes exponent HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection hcoprime hqN test actualDensity` with grid volume $\mathrm{gridVolume}$ (a sum over grids and average over CRT residues of a rational inactive forecast weight divided by $\mathrm{gridVolume}$, times the integral of `test` against Lebesgue measure with density `actualDensity`). Then
--   $$\|\texttt{sourceMean} - \texttt{rationalReference}\| \le \texttt{allocatedSlicedPhysicalComparisonError B U basis S ξ HG H q},$$
--   the error being taken with parameters $t, \varepsilon, \eta, K_\varphi$; explicitly it equals
--   $$\Bigl(\sum_j \tfrac{q}{H(j)} + 2\bigl((2c_0 + 2K) \textstyle\sum_j \tfrac{q}{H(j)} + K \varepsilon\bigr) + 2\eta\Bigr) + (1 + 2(2c_0 + K_\varphi) + K_\varphi) \sum_g \tfrac{q}{H_G(g)} + K_\varphi \xi,$$
--   where $K = K_\varphi \cdot$ `allocatedOriginalSampleFullSliceLip B U basis S t`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B244` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_physical_rational_density_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B244

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
local notation "sourceMean" => allocatedSlicedPhysicalSourceMean B U basis S HP stepP cP hinsideP hHP
  τ box integerFrame HG hHG cG stepG hcontainedG sample H c hH hsubset q selected base deck projection test
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base deck projection
  hcoprime hqN (gridVolume := gridVolume) test actualDensity
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Kφ)

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hshort hp hV htest hbound hτ hξ hbox hframe in
theorem allocatedFixedPath_sliced_physical_rational_density_comparison_s2 :
    ‖sourceMean - rationalReference‖ ≤ comparisonError := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
