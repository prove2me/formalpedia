-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_ambient_rational_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:01:40.889344+00:00
-- url     : https://prove2.me/theorems/4fced7e2-c0c9-4538-973d-eb433c7a9051
-- title:
--   Comparison of the twisted sliced physical forecast target on a fixed path with its rational CRT reference mean
-- statement:
--   This is a technical estimate in OpenAI's forecast machinery with a long list of hypotheses; all named functions and structures below are defined by OpenAI.
--
--   **Data.** Let $m$ be a natural number; $G, T, X$ finite types; $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types; $n : \mathrm{Fin}\ m \to \mathbb{N}$; $B$ a family of finite types indexed by `LayerSamplerAxis I n`; $J$ a family of finite types indexed by $\mathrm{Fin}\ m$; $U_j$ a real subspace of $J_j \to \mathbb{R}$; $\mathrm{basis}_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`, whose $\mathbb{Z}$-span is `projectedIntegerLattice (euclideanSubspace (U j))` (hypothesis $hb$); $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I\ j$; $E$ a family of finite types indexed by $\mathrm{Fin}\ m$ and $bW_j$ a $\mathbb{Z}$-basis indexed by $E\ j$ of the lattice `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, which is assumed to be a $\mathbb{Z}$-lattice in the real span; $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$; $S$ a `LayerSamplerScale B U basis R σ` with positive natural number $L = $ `S.value`. Write "short" for the predicate `allocatedShortAxis U basis S.value` on axes, "Active" for the axes that are not short, $K_{\mathrm{act}}$ for the type $\Sigma_{a \in \mathrm{Active}}\, B\ a \times \mathrm{Fin}\ (\texttt{layerSamplerDegree I n}\ a)$, and $W_0$ = `allocatedPhysicalRootBudget B U basis S (fun _ => 0)`. Let $\mathrm{PrimeIndex}$ be a finite type and $\mathrm{primes}, \mathrm{exponent} : \mathrm{PrimeIndex} \to \mathbb{N}$ with every $\mathrm{primes}(l) \ne 0$, such that the numbers $\mathrm{primes}(l)^{\mathrm{exponent}(l)}$ are pairwise coprime; put $N_{\mathrm{crt}} = \prod_l \mathrm{primes}(l)^{\mathrm{exponent}(l)}$. (That the $\mathrm{primes}(l)$ are prime is not assumed.)
--
--   **Hypotheses.**
--   1. $HP, \mathrm{step}P : $ `PrincipalTupleIndex B (layerSamplerDegree I n)` $\to \mathbb{N}$ and $cP$ to $\mathbb{Z}$, with $0 \le cP_j + \mathrm{step}P_j\, v < $ `allocatedPrincipalSides B U basis S j` for all $j$ and $v < HP_j$, and $HP_j > 0$ for all $j$.
--   2. Reals $\tau > 0$, $\xi > 0$; $\mathrm{box} : X \to \mathbb{N}$ with all $\mathrm{box}(x) > 0$; an integer frame $\mathrm{integerFrame} : \mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X \to \mathbb{Z}$ lying in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W₀ τ ξ box) 1`.
--   3. $HG : G \to \mathbb{N}$ with $HG(g) \ge 2$; $cG : G \to \mathbb{Z}$; $\mathrm{step}G \in \mathbb{N}$ with $\mathrm{step}G > 0$; and for every $g$, `integerProgressionSupport (cG g) stepG (HG g)` (the progression $\{cG(g) + \mathrm{step}G\cdot v : 0 \le v < HG(g)\}$) is contained in $[0, L)$.
--   4. An equivalence $e : G \simeq X \oplus (X \oplus T)$ such that the matrices `fixedSpatialKernelBlock e W₀ L (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false` and the same with `true` have nonzero determinant (hypotheses $h_0, h_1$); and $|B\ a| \ge 4$ for every active axis $a$.
--   5. A coefficient sample `sample : CoefficientSamplerArrays I n` such that for every $j$, `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` holds (the sample lies in the support of the layer's mixed density).
--   6. $H : K_{\mathrm{act}} \to \mathbb{N}$ with all $H_j \ge 2$, $c : K_{\mathrm{act}} \to \mathbb{Z}$, and a real $\delta > 0$, such that for every $j$, `integerProgressionSupport (c j) stepG (H j)` is contained in $[0, L)$ and has at least $\delta L$ elements.
--   7. A natural number $q \ne 0$ dividing $N_{\mathrm{crt}}$.
--   8. Reals $\mathrm{periodCap}, \mathrm{coverCap}$, $\mathrm{Lip} \in \mathbb{R}_{\ge 0}$ and a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` $W$ (a structure bundling a modulus, a cover, a bounded mask and a bounded $\mathrm{Lip}$-Lipschitz smooth function), with $0 < m$, `W.modulus` dividing $q$ and `W.cover` dividing $q$.
--   9. $x_{\mathrm{ref}} : G \to$ `IntegerScalarCubeBox Empty S.value`, $\mathrm{base} : X \to \mathbb{Z}$, and $\mathrm{read} :$ `AllocatedActualCoefficientIndex G X I E n B` $\to \mathbb{Z}$.
--   10. Real-valued vector polynomials $\mathrm{nativePoly}_j$ on $X$ with values in $J_j \to \mathbb{R}$, all coefficients of $\mathrm{nativePoly}_j$ lying in $U_j$ (hypothesis $hmem$), and each $\mathrm{nativePoly}_j$ of degree at most $j + 1$.
--   11. For every $j$ a left-invariant probability measure $\nu_j$ on the quotient of `euclideanSubspace (U j)` by the lattice above; the space `EuclideanJetLayers U (fun _ => Unit)` is compact; $\sigma_{a_1} \le 1$ for every `AllocatedShortIntegerAxis U basis S.value` $a$ (with layer index $a_1$).
--   12. $\mathrm{radius} \in \mathbb{R}_{\ge 0}$ with $\mathrm{radius} > 0$, $3 \le \mathrm{radius}$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)}| \le \mathrm{radius}$ for all $j$.
--   13. $\mathrm{chartCap} : \mathrm{Fin}\ m \to \mathbb{R}$ with $\mathrm{chartCap}_j \ge 0$, $\lVert \phi_j^{-1}(v)\rVert \le \mathrm{chartCap}_j \lVert v \rVert$ for all $j, v$, where $\phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`, and $\mathrm{chartCap}_j\,((|I\ j| + 1)(2\,\mathrm{radius}\,R_j)) \le 1/4$ for all $j$.
--   14. $2\cdot$`spatialTrimMargin τ box i` $\le \mathrm{box}(i)$ for all $i$; $\mathrm{base}$ lies in `trimmedIntegerBox box (spatialTrimMargin τ box)`; and a real $V = \mathrm{gridVolume} > 0$.
--   15. A finite type $\mathrm{Findex}$, reals $pf, cf$, $Lf \in \mathbb{R}_{\ge 0}$, twists $F_i$ (`NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf`), coefficients $\mathrm{nativeCoeff}_i \in \mathbb{C}$ and a real $\delta_{\mathrm{native}}$ such that for all admissible polynomials $\mathrm{poly}$ (coefficients of $\mathrm{poly}_j$ in $U_j$) and all $u : X \to \mathbb{Z}$,
--   $$\Bigl\lVert \kappa\cdot \mathrm{Target}(\mathrm{poly}, u) - \sum_i \mathrm{nativeCoeff}_i\,(F_i).\mathrm{eval}\ \mathrm{box}\ \mathrm{poly}\ u \Bigr\rVert \le \delta_{\mathrm{native}},$$
--   where $\kappa$ = `forecastGeometricJacobian U basis R L V τ` (viewed in $\mathbb{C}$) and $\mathrm{Target}(\mathrm{poly}, u)$ = `forecastLawDensityPhysicalTarget B U basis S law density selected sample xref active output N_crt V base box τ o hb bW poly hpoly u`, with `law` = `principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP`, `density` = `allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c`, `selected` = `allocatedShortIntegerSelection U basis S.value`, `active` the constant CRT input law `crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => (Sum.elim cG c v mod primes l ^ exponent l))`, and `output v` = `integerLongPolynomialOutput (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) v N_crt`.
--   16. Reals $P_{\mathrm{amb}} \ge 0$, $E_{\mathrm{prec}} \ge 0$, $R_{\mathrm{rank}}$, $M$ with: $|X| \le P_{\mathrm{amb}}$; $|\Sigma_j J_j| \le P_{\mathrm{amb}}$; $\mathrm{Lip}\cdot\max(1, cf) + Lf\cdot\max(1, \mathrm{coverCap}) \le e^{P_{\mathrm{amb}}}$ (with $cf$ and $\mathrm{coverCap}$ truncated at $0$); $\texttt{W.cover}\cdot\texttt{(F i).cover} \le e^{P_{\mathrm{amb}}}$ and $\texttt{W.modulus}\cdot\texttt{(F i).modulus} \le e^{P_{\mathrm{amb}}}$ for all $i$; $\sum_i \lVert \mathrm{nativeCoeff}_i \rVert \le M$; and with $Q = \exp\bigl((\max(P_{\mathrm{amb}}, E_{\mathrm{prec}}) + k)^{k}\bigr)$, $k$ = `nativeForecastAmbientExponent m`: $Q \le \mathrm{box}(i)$ for all $i$, $Q \le R_{\mathrm{rank}}$, and `HasLayerSamplingRank (j + 1) box R_rank (U j) (nativePoly j)` for all $j$.
--   17. A natural number $\mathrm{cutoff} > 0$; reals $D \ge 0$, $P_{\mathrm{decay}}$, $\delta_{\mathrm{grid}}$ with $|\texttt{Sigma (AllocatedCongruenceRankOutput X E short)}| + 2 \le P_{\mathrm{decay}}$; for every original tuple $i$ and every additive character $\chi$ of the functions from `Sigma (AllocatedCongruenceRankOutput X E short)` to $\mathbb{Z}/N_{\mathrm{crt}}$, the characteristic function value `finiteImageCharacteristic (active i) (output i mod N_crt) χ` has norm at most $D\cdot \mathrm{ord}(\chi)^{-P_{\mathrm{decay}}}$; $0 \le \delta_{\mathrm{grid}} \le 1$; and $q\cdot\mathrm{cutoff} /$ `forecastJointGridScale U basis R L box τ j` $\le \delta_{\mathrm{grid}}$ for all $j$.
--
--   **Conclusion.**
--   $$\Bigl\lVert \mathbb{E}_{u \in \texttt{integerBox box}}\ \texttt{W.eval box nativePoly}\ u\cdot\bigl(\kappa\cdot \mathrm{Target}(\mathrm{nativePoly}, u)\bigr) - \mathrm{Ref} \Bigr\rVert \le \bigl(2\delta_{\mathrm{native}} + M e^{-E_{\mathrm{prec}}}\bigr) + \mathrm{Err},$$
--   where the expectation is the uniform average over the integer box $\prod_x [0, \mathrm{box}(x))$, $\mathrm{Ref}$ = `allocatedSlicedPhysicalRationalMean B U basis S primes exponent HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample) hcoprime hqN nativeTest density` (with grid volume $V$; a sum over grid points of rational inactive forecasts tested against the integral of `nativeTest` with respect to the density `density`), `nativeTest` = `W.forecastShortGridTest U basis S.value hb o bW R q hm hperiod hcover (fun a => base a / box a) τ`, and $\mathrm{Err}$ = `allocatedSlicedPhysicalAmbientGridError` evaluated at the data $B, U, \mathrm{basis}, S, E, \tau, \xi, \mathrm{box}, \mathrm{integerFrame}, HG, cG, \mathrm{step}G, e, h_0, h_1, \delta, o, \mathrm{Lip}, \mathrm{cutoff}, D, \delta_{\mathrm{grid}}$ (and the other data in scope), an explicit error term.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_ambient_rational_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedAmbientNativeCRTNeZero
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
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "rationalReference" => allocatedSlicedPhysicalRationalMean B U basis S primes exponent
  HP stepP cP hinsideP hHP integerFrame cG stepG sample c q selected xref base
  (allocatedReadDeck read) projection hcoprime hqN (gridVolume := gridVolume) nativeTest actualDensity

local instance slicedAmbientRecoveredCoverNeZero_r3b68c0_1 : NeZero W.cover := ⟨W.cover_pos.ne'⟩
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

local notation "actualLaw" => principalAffineIntervalLaw B degree
  (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP
local notation "actualActive" => (fun _ : Original => crtPolynomialInputLaw primes exponent
  (fun l => padicValNat (primes l) stepG) hcoprime
  (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l))))
local notation "actualOutput" => (fun v : Original => integerLongPolynomialOutput
  (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) projection)
  (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) Ncrt)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I)
  U basis R S.value gridVolume τ : ℝ) : ℂ)
local notation "actualTarget" => forecastLawDensityPhysicalTarget B U basis S actualLaw
  actualDensity selected sample xref actualActive actualOutput Ncrt gridVolume
  base box τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
variable (radius : ℝ≥0) (hradius0 : 0 < radius) (hradius3 : (3 : ℝ) ≤ radius)
variable (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ radius)
variable (chartCap : Fin m → ℝ) (hchartCap : ∀ j, 0 ≤ chartCap j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
  chartCap j * ‖v‖)
variable (hchartBudget : ∀ j, chartCap j * (((Fintype.card (I j) : ℝ) + 1) *
  (2 * (radius : ℝ) * R j)) ≤ 1 / 4)
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ box i ≤ box i)
variable (htrimbase : base ∈ trimmedIntegerBox box (spatialTrimMargin τ box))
variable (hVpos : 0 < gridVolume)
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hpoly : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U basis R S.value gridVolume τ : ℝ) : ℂ) * (forecastLawDensityPhysicalTarget B U basis S (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) HP stepP cP hinsideP hHP) (allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c) (allocatedShortIntegerSelection U basis S.value) sample xref (fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) (fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) (∏ l, primes l ^ exponent l) gridVolume base box τ o hb bW) poly hpoly u - ∑ i, nativeCoeff i * (F i).eval box poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hX : (Fintype.card X : ℝ) ≤ Pambient)
variable (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (box i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (box i : ℝ))
  Rrank (U j) (nativePoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {D Pdecay δgrid : ℝ} (hD : 0 ≤ D)
variable (hPdecay : ((Fintype.card (Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) + 2 : ℕ) : ℝ) ≤ Pdecay)
variable (hdecay : ∀ i (χ : AddChar ((Sigma (AllocatedCongruenceRankOutput X E (allocatedShortAxis (I := I) U basis S.value))) → ZMod (∏ l, primes l ^ exponent l)) ℂ),
  ‖finiteImageCharacteristic ((fun _ : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => crtPolynomialInputLaw primes exponent (fun l => padicValNat (primes l) stepG) hcoprime (fun l v => ((Sum.elim cG c v : ℤ) : ZMod (primes l ^ exponent l)))) i) (fun x j => ((fun v : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) => integerLongPolynomialOutput (allocatedForecastPolynomial (allocatedShortAxis (I := I) U basis S.value) base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) (fun k => (v (Prod.fst k) (Prod.snd k) : ℤ)) (∏ l, primes l ^ exponent l)) i x j : ZMod (∏ l, primes l ^ exponent l))) χ‖ ≤
    D * (orderOf χ : ℝ) ^ (-Pdecay))
variable (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U basis R S.value box τ j ≤ δgrid)

include hR hσ hs hτ hξ hbox hframe hcontainedG hH hδ hsubset hdense ν hlattice hcompact hσ1
  hradius0 hradius3 hradius hchartCap hchart hchartBudget hmargin htrimbase hVpos
  happrox hdegree hPambient hEprec hX hdim hLip hcoverF hmodF hmass hlarge hRrank hrank
  hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh in

theorem allocatedFixedPath_sliced_ambient_rational_comparison_s2 :
    ‖(𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * actualTarget nativePoly hmem u)) - rationalReference‖ ≤
      (2 * δnative + M * Real.exp (-Eprec)) +
        allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := basis) (S := S)
          (E := E) (τ := τ) (ξ := ξ) (box := box) (integerFrame := integerFrame)
          (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG) (hstepG := hstepG)
          (e := e) (h0 := h0) (h1 := h1) (hδ := hδ) (o := o) (Lip := Lip)
          (cutoff := cutoff) (D := D) (δgrid := δgrid) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
