-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_native_ambient_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:59:24.69604+00:00
-- url     : https://prove2.me/theorems/afacc7bc-9867-4e36-a466-5cbea2c756e7
-- title:
--   Native ambient comparison for an actual fixed spatial sliced forecast path
-- statement:
--   **Setting.** Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$, $J_j$, $E^{\mathrm{out}}_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be that subspace inside the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), and let $b_j$ be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement. Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$ (hypotheses hR, hσ), and let $S$ be a `LayerSamplerScale B U b R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $X$ be a finite type with decidable equality, $D_{\mathrm{mod}}$ and $L_{\mathrm{rank}}$ natural numbers, `spatial` an embedding $\operatorname{Fin} L_{\mathrm{rank}} \hookrightarrow G$, `kernel j` embeddings $\operatorname{Fin} L_{\mathrm{rank}} \times \operatorname{Fin}(j+1) \hookrightarrow G$, `block j a` embeddings $\operatorname{Fin} L_{\mathrm{rank}} \hookrightarrow B(j, a)$ for each axis $a$ of layer $j$ that is not short in the sense of `allocatedShortAxis U b S.value` (OpenAI's predicate: an integer axis $(j, i)$ is short when its basis scale is at most $\texttt{S.value}^{j+1}$; real axes are never short), $T_{\mathrm{sp}}$ a finite type, `spatialEquiv` a bijection $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$, $N : X \to \mathbb{N}$ (`physicalN`), and reals $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$.
--
--   Let `slice` be an `ActualFixedSpatialSlicedForecastPath` for all these data, with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)` and length `S.value` (OpenAI's structure: an `ActualFixedSpatialForecastPath` `slice.path` (with a base point, an integer noise frame, sample arrays, a read function, a center in $\prod_j U_j$, a reference modulus, and so on) together with a common step `slice.step` $> 0$, kernel progressions with lengths `slice.kernelLength g` $\ge 2$ and starts, and principal progressions with lengths `slice.principalLength`, steps and starts `slice.principalStart`, all inside the corresponding boxes). Let `s` be an `ActualFixedSpatialForecastSetup` for $B, U, b, S, D_{\mathrm{mod}}$, `allocatedShortIntegerSelection U b S.value`, $\tau$, $\delta_{\mathrm{slice}}$ (OpenAI's structure of dimension and size parameters, including reals `s.P` and `s.L`). Let $hb$: for each $j$ the integer span of $b_j$ equals `projectedIntegerLattice` (the projection of $\mathbb{Z}^{J_j}$ onto the orthogonal complement; defined by OpenAI); let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$; and let $bW_j$ be a $\mathbb{Z}$-basis, indexed by $E^{\mathrm{out}}_j$, of `latticeSection` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`). Let $W$ be a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (OpenAI's structure: a positive modulus at most periodCap, a positive cover at most coverCap, a mask on $(\mathbb{Z}/\text{modulus})^X$ of norm at most $1$, and a smooth function of norm at most $1$ and Lipschitz constant Lip; `W.eval N p u` $=$ mask$(u \bmod \text{modulus}) \cdot$ smooth$(u/N, \text{grid factor input of } p \text{ at } u)$). Let `originalpoly j` be vector polynomials in the variables $X$ with values in $J_j \to \mathbb{R}$, with every coefficient in $U_j$ (hmem) and total degree at most $j+1$ (hdegree).
--
--   **Hypotheses.** Assume the following (Lean names in parentheses).
--   - (hξ) $\xi > 0$; (hbox) $N_x > 0$ for all $x$; (hframe) `slice.path.noise` lies in `rectangularWeightIndices 0 w 1`, where $w$ = `narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N` (OpenAI's widths).
--   - (ht) $t > 0$; (hσbound) $|\sigma_j| \le t$ for all $j$; (hδ, hδone) $0 < \delta \le 1$.
--   - (hdense) for every non-short axis $a$ and every $p \in B(a) \times \operatorname{Fin}(\text{degree of } a)$, $\delta \cdot \texttt{S.value} \le$ the cardinality of `integerProgressionSupport` (the progression with start `slice.principalStart (a, p)`, step `slice.step` and length `slice.principalLength (a, p)`).
--   - $q$ a nonzero natural number with (hperiod) `W.modulus` $\mid q$, (hcover) `W.cover` $\mid q$, (hqN) $q \mid$ `slice.path.referenceModulus`; (hsizeG) $q \le$ `slice.kernelLength g` for all $g$; (hsmallG) $c \cdot q / \texttt{slice.kernelLength } g < 1$ for all $g$, where $c$ = `scalarCubeGridBoundaryConstant Empty` (an explicit constant of OpenAI); (hsize) $q \le$ `slice.principalLength (a, p)` and (hsmall) $c \cdot q / \texttt{slice.principalLength } (a, p) < 1$ for every non-short axis $a$ and every $p$ as above.
--   - (hε) $\varepsilon \ge 0$; (hmesh) `slice.step` $/ \texttt{S.value} \le \varepsilon$; (hη) $\eta > 0$.
--   - (htail) $|t| \cdot$ `polynomialMassC2Budget K m 1` $\le$ `slicedPrincipalC2Tolerance K K' m 1 (unitProfilePrincipalLowerBound B) (δ / 2) s.L η`, where $K$ is the number of pairs (non-short axis $a$, element of $B(a) \times \operatorname{Fin}(\text{degree of } a)$), $K'$ is the number of non-short axes, and the three functions are explicit real-valued functions of OpenAI.
--   - (hVpos) `gridVolume` $> 0$; a family $\nu_j$ of left-invariant probability measures on the quotient of `euclideanSubspace (U j)` by `latticeSection`; each `latticeSection` is a full lattice (hlattice); the space `EuclideanJetLayers U (fun _ => Unit)` is compact (hcompact).
--   - (hmargin) $2 \cdot$ `spatialTrimMargin τ N x` $\le N_x$ for all $x$, where `spatialTrimMargin τ N x` $= \lceil \tau N_x / 4 \rceil$; (htrimbase) `slice.path.base` lies in `trimmedIntegerBox N (spatialTrimMargin τ N)` (the integer box $\prod_x [0, N_x)$ with the margin removed on both sides).
--   - A finite type `Findex`, twists $F_i$ = `NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf`, complex numbers `nativeCoeff i` and a real $\delta_{\mathrm{native}}$ such that (happrox): for every family `poly` of vector polynomials with coefficients in $U_j$ and every $u \in \mathbb{Z}^X$,
--   $\bigl\lVert \kappa \cdot \texttt{referenceTarget poly}(u) - \sum_i \texttt{nativeCoeff}_i \cdot F_i.\texttt{eval } N\ \texttt{poly}\ u \bigr\rVert \le \delta_{\mathrm{native}}$.
--   Here $\kappa$ = `forecastGeometricJacobian U b R S.value gridVolume τ` (an explicit positive normalising constant of OpenAI), and `referenceTarget` is `forecastLawDensityPhysicalTarget B U b S slice.principalLaw (slice.density s.hBactive) (allocatedShortIntegerSelection U b S.value) slice.path.sample slice.path.commonTuple (fun _ => slice.path.referenceInputLaw) (fun y => integerLongPolynomialOutput slice.path.referencePolynomial y slice.path.referenceModulus) slice.path.referenceModulus gridVolume slice.path.base N τ o hb bW` (OpenAI's complex density target at a physical point).
--   - Reals $P_{\mathrm{amb}} \ge 0$ (hPambient), $E_{\mathrm{prec}} \ge 0$ (hEprec), $R_{\mathrm{rank}}$ and $M$ with (hPP) `s.P` $\le P_{\mathrm{amb}}$; (hLip) $\mathrm{Lip} \cdot \max(1, cf) + Lf \cdot \max(1, \mathrm{coverCap}) \le e^{P_{\mathrm{amb}}}$; (hcoverF) `W.cover` $\cdot F_i$`.cover` $\le e^{P_{\mathrm{amb}}}$ and (hmodF) `W.modulus` $\cdot F_i$`.modulus` $\le e^{P_{\mathrm{amb}}}$ for all $i$; (hmass) $\sum_i \lVert \texttt{nativeCoeff}_i \rVert \le M$; (hlarge) $\exp\bigl((\max(P_{\mathrm{amb}}, E_{\mathrm{prec}}) + k)^k\bigr) \le N_x$ for all $x$ and (hRrank) the same quantity is $\le R_{\mathrm{rank}}$, where $k$ = `nativeForecastAmbientExponent m` (a natural number chosen by OpenAI); (hrank) for each $j$, `HasLayerSamplingRank (j+1) N R_rank (U j) (originalpoly j)` (OpenAI's predicate: no nonzero integer functional of size at most $R_{\mathrm{rank}}$ that is nonzero on $U_j$ makes `originalpoly j` admit a rational approximation of the kind defined by OpenAI's `PolynomialRationalApproximation`).
--   - A natural number `cutoff` $> 0$ and a real $\delta_{\mathrm{grid}} \in [0, 1]$ with (hgridmesh) $q \cdot \mathrm{cutoff} / \texttt{forecastJointGridScale U b R S.value N tau}(j) \le \delta_{\mathrm{grid}}$ for every index $j$ (the grid scale is $\tau N_x / 8$ on physical coordinates and an OpenAI-defined active integer grid scale on the others).
--   - A real $C$, a point `center` of `CoefficientTorus U`, and functions `sampleFn`, `readFn` of the noise frame, such that (hglobal) `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center slice.path.center slice.path.base sampleFn readFn` holds (OpenAI's recovery predicate), (hz) `allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem center slice.path.base slice.path.noise` $\ne 0$, (hsampleAt) `sampleFn slice.path.noise` $=$ `slice.path.sample`, and (hreadAt) `readFn slice.path.noise` $=$ `slice.path.read`.
--
--   **Conclusion.** Let $p$ = `slice.path.physicalPolynomial originalpoly`, the family `originalpoly j` minus the constant `slice.path.center j`. Then
--   $$\Bigl\lVert \texttt{slice.nativeMean s W originalpoly} - \mathbb{E}_{u \in \texttt{integerBox } N}\bigl[ W.\texttt{eval } N\ p\ u \cdot \bigl(\kappa \cdot \texttt{referenceTarget } p\ (u)\bigr) \bigr] \Bigr\rVert \le \texttt{slice.comparisonError},$$
--   where the expectation is the uniform average over the integer box $\prod_x [0, N_x)$, `slice.nativeMean s W originalpoly` is OpenAI's complex mean of $W$ evaluated along the sliced native sampling law of the path, and `slice.comparisonError` (with the parameters Lip, $\xi$, $t$, $\delta$, $\varepsilon$, $\eta$, $q$, $o$, $\delta_{\mathrm{native}}$, $M$, $E_{\mathrm{prec}}$, cutoff, $\delta_{\mathrm{grid}}$) is OpenAI's explicit error term: the sum of `allocatedSlicedPhysicalComparisonError`, $2\delta_{\mathrm{native}} + M e^{-E_{\mathrm{prec}}}$, and `allocatedSlicedPhysicalAmbientGridError`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_comparison)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : slice.path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ slice.path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ slice.kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ slice.principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / slice.principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (slice.step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}
local notation "selected" => allocatedShortIntegerSelection U b S.value
local notation "Original" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S)

attribute [local instance] OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.actualComparisonReferenceNeZero
variable (gridVolume : ℝ) (hVpos : 0 < gridVolume)
local notation "κ" => ((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ)
local notation "referenceTarget" => forecastLawDensityPhysicalTarget B U b S slice.principalLaw
  (slice.density s.hBactive) selected slice.path.sample slice.path.commonTuple
  (fun _ : Original => slice.path.referenceInputLaw)
  (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
    (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
  slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
variable {Findex : Type} [Fintype Findex] {pf cf : ℝ} {Lf : ℝ≥0}
variable (F : Findex → NormalizedPolynomialTwist X (Σ j, J j) pf cf Lf)
variable (nativeCoeff : Findex → ℂ) (δnative : ℝ)
variable (happrox : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hp : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((forecastGeometricJacobian (X := X) (I := I) U b R S.value gridVolume τ : ℝ) : ℂ) *
    forecastLawDensityPhysicalTarget B U b S slice.principalLaw (slice.density s.hBactive)
      (allocatedShortIntegerSelection U b S.value) slice.path.sample slice.path.commonTuple
      (fun _ : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U b S) =>
        slice.path.referenceInputLaw)
      (fun y => integerLongPolynomialOutput slice.path.referencePolynomial
        (fun k => (y (Prod.fst k) (Prod.snd k) : ℤ)) slice.path.referenceModulus)
      slice.path.referenceModulus gridVolume slice.path.base physicalN τ o hb bW poly hp u -
    ∑ i, nativeCoeff i * (F i).eval physicalN poly u‖ ≤ δnative)
variable {Pambient Eprec Rrank M : ℝ} (hPambient : 0 ≤ Pambient) (hEprec : 0 ≤ Eprec)
variable (hPP : s.P ≤ Pambient)
variable (hLip : ((Lip * max 1 (Real.toNNReal cf) + Lf * max 1 (Real.toNNReal coverCap) : ℝ≥0) : ℝ) ≤ Real.exp Pambient)
variable (hcoverF : ∀ i, ((W.cover * (F i).cover : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmodF : ∀ i, ((W.modulus * (F i).modulus : ℕ) : ℝ) ≤ Real.exp Pambient)
variable (hmass : ∑ i, ‖nativeCoeff i‖ ≤ M)
variable (hlarge : ∀ i, Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max Pambient Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)

variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center slice.path.center slice.path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center slice.path.base slice.path.noise ≠ 0)
variable (hsampleAt : sampleFn slice.path.noise = slice.path.sample)
variable (hreadAt : readFn slice.path.noise = slice.path.read)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail hVpos ν hlattice hcompact
  hmargin htrimbase happrox hPambient hEprec hPP hLip hcoverF hmodF hmass hlarge
  hRrank hrank hcutoff hδgrid hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt in

theorem native_ambient_comparison_s2 :
    ‖slice.nativeMean s W originalpoly -
      (𝔼 u ∈ integerBox physicalN,
        W.eval physicalN (slice.path.physicalPolynomial originalpoly) u *
          (κ * referenceTarget (slice.path.physicalPolynomial originalpoly)
            (slice.path.physicalPolynomial_mem originalpoly hmem) u))‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := δnative) (M := M) (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
