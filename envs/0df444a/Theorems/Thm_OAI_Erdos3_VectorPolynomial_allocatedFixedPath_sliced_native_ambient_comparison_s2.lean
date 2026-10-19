-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPath_sliced_native_ambient_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:11:21.070841+00:00
-- url     : https://prove2.me/theorems/dc8127cc-a961-4149-aa5c-8114e8b66024
-- title:
--   Native ambient comparison for the allocated fixed-path sliced sampler
-- statement:
--   **Setting.** Let $m$ be a natural number and $G$, $T$, $X$ finite types. For $j \in \operatorname{Fin} m$ let $I_j$, $J_j$, $E_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be that subspace in the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), and let `basis j` be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement. Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ (hR, hσ), and let $S$ be a `LayerSamplerScale B U basis R σ` (OpenAI's structure containing a positive natural number `S.value`). Call an axis short if it satisfies OpenAI's predicate `allocatedShortAxis U basis S.value` (an integer axis $(j, i)$ whose basis scale is at most $\texttt{S.value}^{j+1}$; real axes are never short), and write `Active` for the type of pairs (non-short axis $a$, element of $B(a) \times \operatorname{Fin}(\text{degree of } a)$), where the degree of an axis of layer $j$ is $j+1$.
--
--   Let `PrimeIndex` be a finite type, and `primes`, `exponent` natural-number functions on it with every `primes l` nonzero; write $N_{\mathrm{crt}} = \prod_l \texttt{primes}_l^{\texttt{exponent}_l}$. Let $H_P, \mathrm{step}_P$ (natural numbers) and $c_P$ (integers) be functions on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H_P > 0$ and $0 \le c_P(j) + \mathrm{step}_P(j)\, v < $ `allocatedPrincipalSides B U basis S j` for all $v < H_P(j)$ (hinsideP).
--
--   The remaining data and hypotheses are as follows (Lean names in parentheses).
--   - (hτ) $\tau > 0$; (hξ) $\xi > 0$; `box` $: X \to \mathbb{N}$ with (hbox) all values positive; an integer frame on $\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X$ lying in (hframe) `rectangularWeightIndices 0 w 1` with $w$ = `narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) τ ξ box`.
--   - $H_G : G \to \mathbb{N}$ with $H_G(g) \ge 2$; $c_G : G \to \mathbb{Z}$; $\mathrm{step}_G > 0$; (hcontainedG) each progression `integerProgressionSupport (cG g) stepG (HG g)` (the integers $c_G(g) + \mathrm{step}_G k$, $0 \le k < H_G(g)$) lies in $[0, \texttt{S.value})$.
--   - A bijection $e : G \simeq X \sqcup (X \sqcup T)$ such that (h0, h1) both blocks `fixedSpatialKernelBlock e (allocatedPhysicalRootBudget B U basis S (fun _ => 0)) S.value (allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame) false` and the same with `true` (square $X \times X$ matrices defined by OpenAI) have nonzero determinant.
--   - (hB) $|B(a)| \ge 4$ for every non-short axis $a$.
--   - Sample arrays `sample` in `CoefficientSamplerArrays I n` with (hs) `mixedArraySupported (allocatedLayerCenters B U basis S j) (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)` for all $j$ (the sample lies in the support of OpenAI's layer densities).
--   - (ht) $t > 0$; (hσbound) $|\sigma_j| \le t$ for all $j$.
--   - $H : \texttt{Active} \to \mathbb{N}$ and $c : \texttt{Active} \to \mathbb{Z}$ with (hH) $H \ge 2$; (hδ) $\delta > 0$; (hsubset) `integerProgressionSupport (c j) stepG (H j)` $\subseteq [0, \texttt{S.value})$; (hdense) $\delta \cdot \texttt{S.value} \le |\texttt{integerProgressionSupport}(c(j), \mathrm{step}_G, H(j))|$; (hδone) $\delta \le 1$.
--   - A nonzero natural number $q$ with (hsizeG) $q \le H_G(g)$ and (hsmallG) $\kappa_0 q / H_G(g) < 1$ for all $g$, and (hsize) $q \le H(j)$ and (hsmall) $\kappa_0 q / H(j) < 1$ for all $j \in$ `Active`, where $\kappa_0$ = `scalarCubeGridBoundaryConstant Empty` (an explicit constant of OpenAI).
--   - (hε) $\varepsilon \ge 0$; (hmesh) $\mathrm{step}_G / \texttt{S.value} \le \varepsilon$ (stated for each $j \in$ `Active`).
--   - $b$, a choice of an element $b(a) \in B(a)$ for each non-short axis $a$.
--   - (hη) $\eta > 0$; $A \in \mathbb{R}_{\ge 0}$ with (hA) Mathlib's `Real.smoothTransition` $A$-Lipschitz; (htail) $|t| \cdot$ `polynomialMassC2Budget K m 1` $\le$ `slicedPrincipalC2Tolerance K K' m 1 (unitProfilePrincipalLowerBound B) (δ/2) A η`, where $K = |\texttt{Active}|$, $K'$ is the number of non-short axes, and the three functions are explicit real-valued functions of OpenAI.
--   - (hb) the integer span of `basis j` equals `projectedIntegerLattice` (the projection of $\mathbb{Z}^{J_j}$ onto the orthogonal complement); $o_j$ an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$; $bW_j$ a $\mathbb{Z}$-basis, indexed by $E_j$, of `latticeSection` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`).
--   - $W$, a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (OpenAI's structure: a positive modulus at most periodCap, a positive cover at most coverCap, a mask on $(\mathbb{Z}/\text{modulus})^X$ of norm at most $1$, and a smooth function of norm at most $1$ that is Lip-Lipschitz; `W.eval N p u` $=$ mask$(u \bmod \text{modulus}) \cdot$ smooth$(u/N, \text{grid factor input of } p \text{ at } u)$), with (hm) $m > 0$, (hperiod) `W.modulus` $\mid q$ and (hcover) `W.cover` $\mid q$.
--   - $x_{\mathrm{ref}} : G \to$ `IntegerScalarCubeBox Empty S.value`; `base` $\in \mathbb{Z}^X$; `read` an integer function on `AllocatedActualCoefficientIndex G X I E n B` (an index type of OpenAI); (hp) each `primes l` is prime; (hcoprime) the prime powers $\texttt{primes}_l^{\texttt{exponent}_l}$ are pairwise coprime; (hqN) $q \mid N_{\mathrm{crt}}$; (hV) `gridVolume` $\ne 0$.
--   - Vector polynomials `nativePoly j` in the variables $X$ with values in $J_j \to \mathbb{R}$, with (hmem) all coefficients in $U_j$ and (hdegree) total degree at most $j+1$; (hbase) `canonicalCoefficientSample U basis hb o sample` $=$ `affineSampleCoefficientTorus U nativePoly hmem` evaluated at the real points `integerBaseTranslation base + integerFrame` (both points of OpenAI's coefficient torus); (hsmallChart) $|\texttt{coefficientSamplerAmbientPoint U basis o sample}(a)| < 1/2$ for every index $a$; (hread) for every event on `CoefficientChartResidues (LayerSamplerVariables G I n B) n E W.cover`, `coefficientDeckChartEvent U bW basis hb o W.cover event` holds at `affineCoefficientCoverSample U nativePoly hmem W.cover (integerBaseTranslation base + integerFrame)` if and only if the event holds at `allocatedReadCoefficientChartResidues` of `read` reduced modulo `W.cover`.
--   - Each `latticeSection` is a full lattice (hlattice); $\nu_j$ left-invariant probability measures on the quotient of `euclideanSubspace (U j)` by `latticeSection`; `EuclideanJetLayers U (fun _ => Unit)` compact (hcompact).
--   - (hσ1) $\sigma_j \le 1$ for the layer $j$ of every short integer axis; $\mathrm{radius} \in \mathbb{R}_{\ge 0}$ with $\mathrm{radius} > 0$, $\mathrm{radius} \ge 3$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \le \mathrm{radius}$ for all $j$; `chartCap` $: \operatorname{Fin} m \to \mathbb{R}$ nonnegative with $\lVert \Phi_j^{-1}(v) \rVert \le \texttt{chartCap}_j \lVert v \rVert$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)`, and $\texttt{chartCap}_j (|I_j| + 1)(2\,\mathrm{radius}\, R_j) \le 1/4$.
--   - (hmargin) $2 \cdot$ `spatialTrimMargin τ box i` $\le \texttt{box}_i$ for all $i$, where `spatialTrimMargin τ N i` $= \lceil \tau N_i / 4 \rceil$; (htrimbase) `base` $\in$ `trimmedIntegerBox box (spatialTrimMargin τ box)`; (hVpos) `gridVolume` $> 0$.
--   - Let `actualTarget` be `forecastLawDensityPhysicalTarget B U basis S actualLaw actualDensity (allocatedShortIntegerSelection U basis S.value) sample xref actualActive actualOutput N_crt gridVolume base box τ o hb bW` (OpenAI's complex density target at a physical point), where `actualLaw` = `principalAffineIntervalLaw` of $(H_P, \mathrm{step}_P, c_P)$ (the image of the uniform law on $\prod_j [0, H_P(j))$ under the affine progression map), `actualDensity` = `allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c`, `actualActive` is the constant family `crtPolynomialInputLaw primes exponent (l ↦ v_{primes l}(stepG)) hcoprime (origins from cG and c)`, and `actualOutput v` = `integerLongPolynomialOutput (allocatedForecastPolynomial short base integerFrame (allocatedReadDeck read) (allocatedOriginalSampleCongruenceProjection B U basis S sample)) v N_crt` (all defined by OpenAI). Let $\kappa$ = `forecastGeometricJacobian U basis R S.value gridVolume τ` (an explicit normalising constant of OpenAI).
--   - A finite type `Findex`, twists $F_i$ = `NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf`, complex numbers `nativeCoeff i` and a real $\delta_{\mathrm{native}}$ with (happrox): for every family `poly` with coefficients in $U_j$ and every $u \in \mathbb{Z}^X$, $\bigl\lVert \kappa \cdot \texttt{actualTarget poly}(u) - \sum_i \texttt{nativeCoeff}_i \cdot F_i.\texttt{eval box poly } u \bigr\rVert \le \delta_{\mathrm{native}}$.
--   - Reals $P_{\mathrm{amb}} \ge 0$, $E_{\mathrm{prec}} \ge 0$, $R_{\mathrm{rank}}$, $M$ with (hX) $|X| \le P_{\mathrm{amb}}$; (hdim) $\sum_j |J_j| \le P_{\mathrm{amb}}$; (hLip) $\mathrm{Lip} \cdot \max(1, cf) + Lf \cdot \max(1, \mathrm{coverCap}) \le e^{P_{\mathrm{amb}}}$; (hcoverF, hmodF) `W.cover` $\cdot F_i$`.cover` $\le e^{P_{\mathrm{amb}}}$ and `W.modulus` $\cdot F_i$`.modulus` $\le e^{P_{\mathrm{amb}}}$ for all $i$; (hmass) $\sum_i \lVert \texttt{nativeCoeff}_i \rVert \le M$; (hlarge) $\exp((\max(P_{\mathrm{amb}}, E_{\mathrm{prec}}) + k)^k) \le \texttt{box}_i$ for all $i$, and (hRrank) the same quantity is $\le R_{\mathrm{rank}}$, with $k$ = `nativeForecastAmbientExponent m` (a natural number chosen by OpenAI); (hrank) `HasLayerSamplingRank (j+1) box R_rank (U j) (nativePoly j)` for each $j$ (OpenAI's predicate excluding a rational approximation of `nativePoly j` along any integer functional of size at most $R_{\mathrm{rank}}$ that is nonzero on $U_j$).
--   - `cutoff` $> 0$; reals $D \ge 0$, $P_{\mathrm{decay}}$ and $\delta_{\mathrm{grid}} \in [0, 1]$ with (hPdecay) $|\text{output index type}| + 2 \le P_{\mathrm{decay}}$, where the output index type is `Sigma (AllocatedCongruenceRankOutput X E short)`; (hdecay) for every principal tuple $i$ and every additive character $\chi$ of $(\mathbb{Z}/N_{\mathrm{crt}})^{\text{outputs}}$, the norm of `finiteImageCharacteristic` (the mean of $\chi(\texttt{actualOutput } i\ x)$ over $x \sim$ `actualActive i`) is at most $D \cdot \operatorname{ord}(\chi)^{-P_{\mathrm{decay}}}$; (hgridmesh) $q \cdot \mathrm{cutoff} / \texttt{forecastJointGridScale U basis R S.value box tau}(j) \le \delta_{\mathrm{grid}}$ for every grid index $j$.
--
--   **Conclusion.**
--   $$\Bigl\lVert \texttt{allocatedSlicedNativeEvalMean}(\dots) - \mathbb{E}_{u \in \texttt{integerBox box}} \bigl[ W.\texttt{eval box nativePoly } u \cdot (\kappa \cdot \texttt{actualTarget nativePoly}(u)) \bigr] \Bigr\rVert \le \mathcal{E}_1 + \bigl( (2\delta_{\mathrm{native}} + M e^{-E_{\mathrm{prec}}}) + \mathcal{E}_2 \bigr).$$
--   Here `allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset` is OpenAI's complex mean of `W.eval box nativePoly` at the physical sites `base` $+$ `integerPhysicalSite` (root, `integerFrame`), averaged over the inactive affine interval law of $(H_P, \mathrm{step}_P, c_P)$, uniform kernel cubes embedded in the progressions $(c_G, \mathrm{step}_G, H_G)$, and uniform active cubes embedded in the progressions $(c, \mathrm{step}_G, H)$; the expectation is uniform over $\prod_x [0, \texttt{box}_x)$; $\mathcal{E}_1$ = `allocatedSlicedPhysicalComparisonError B U basis S ξ HG H q` with parameters $t, \varepsilon, \eta$ and $K_\varphi = \mathrm{Lip} \cdot \max(|\tau/8|, \texttt{forecastNativeAmbientLip U basis o R})$; and $\mathcal{E}_2$ = `allocatedSlicedPhysicalAmbientGridError` with the parameters $\tau, \xi$, box, integerFrame, $H_G$, $c_G$, $\mathrm{step}_G$, $e$, $\delta$, $o$, Lip, cutoff, $D$, $\delta_{\mathrm{grid}}$ (explicit real error terms of OpenAI).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison` (in `lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFixedPath_sliced_native_ambient_comparison)

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
local notation "degree" => layerSamplerDegree I n

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local notation "Original" => PrincipalIntegerTuples B degree Empty (allocatedPrincipalSides B U basis S)
attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedCompleteNativeCRTNeZero
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
local notation "Knative" => Lip * max ‖τ / 8‖₊ (forecastNativeAmbientLip U basis o R)
local notation "actualDensity" => allocatedSlicedPhysicalForecastDensity B U basis S τ ξ box
  integerFrame HG hHG cG stepG hstepG e h0 h1 hB sample H c
local notation "projection" => allocatedOriginalSampleCongruenceProjection B U basis S sample
local notation "comparisonError" => allocatedSlicedPhysicalComparisonError B U basis S ξ HG
  (t := t) H q (ε := ε) (η := η) (Kφ := Knative)

attribute [local instance] OAI.Erdos3.VectorPolynomial.slicedCompleteRecoveredCoverNeZero
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

include hR hσ hs ht hσbound hδ hsubset hdense hsizeG hsmallG hsize hsmall hε hmesh
  hδone b hη hA htail hp hV hτ hξ hbox hframe hmem hdegree hbase hsmallChart hread
  hm hperiod hcover hqN ν hlattice hcompact hσ1 hradius0 hradius3 hradius hchartCap hchart hchartBudget
  hmargin htrimbase hVpos happrox hPambient hEprec hX hdim hLip hcoverF hmodF hmass
  hlarge hRrank hrank hcutoff hD hPdecay hdecay hδgrid hδgrid1 hgridmesh in

theorem allocatedFixedPath_sliced_native_ambient_comparison_s2 :
    ‖allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
        HP stepP cP hinsideP hHP HG hHG cG stepG hcontainedG H c hH hsubset -
      (𝔼 u ∈ integerBox box, W.eval box nativePoly u *
        (κ * actualTarget nativePoly hmem u))‖ ≤
      comparisonError + ((2 * δnative + M * Real.exp (-Eprec)) +
        allocatedSlicedPhysicalAmbientGridError (B := B) (U := U) (basis := basis) (S := S)
          (E := E) (τ := τ) (ξ := ξ) (box := box) (integerFrame := integerFrame)
          (HG := HG) (hHG := hHG) (cG := cG) (stepG := stepG) (hstepG := hstepG)
          (e := e) (h0 := h0) (h1 := h1) (hδ := hδ) (o := o) (Lip := Lip)
          (cutoff := cutoff) (D := D) (δgrid := δgrid)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
