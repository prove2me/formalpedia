-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialSlicedForecastPath_native_ambient_model_comparison_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:38.454953+00:00
-- url     : https://prove2.me/theorems/b6f7dbcd-f8fd-4ca8-bd5a-69c51cbbe95a
-- title:
--   For an actual fixed spatial sliced forecast path, the native mean is close to the uniform box mean of the twisted model times the forecast target
-- statement:
--   This statement lives in a large context of OpenAI's sliced forecast machinery; all objects named in backticks below are defined by OpenAI, and the hypothesis names in parentheses are those of the Lean statement.
--
--   **Data.** Let $m$ be a natural number, $G$ a finite type, and for $j \in \operatorname{Fin} m$ let $I_j$ and $J_j$ be finite types and $n_j$ a natural number. Let `LayerSamplerAxis I n` be the type of pairs $(j, a)$ with $j \in \operatorname{Fin} m$ and $a \in I_j \sqcup \operatorname{Fin} n_j$, and let $B$ assign a finite type $B_a$ to each such axis $a$. For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be the same subspace inside the Euclidean space $\mathbb{R}^{J_j}$, and let $b_j$ be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement. Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$ (hR, hσ), and let $S$ be a `LayerSamplerScale B U b R σ` (a positive natural number `S.value` satisfying OpenAI's width and gap conditions). Let $X$ be a finite type with decidable equality, $E^{\mathrm{out}}_j$ finite types, $\mathrm{Dmod}$ and $\mathrm{Lrank}$ natural numbers, $\mathrm{spatial} : \operatorname{Fin} \mathrm{Lrank} \hookrightarrow G$, $\mathrm{kernel}_j : \operatorname{Fin} \mathrm{Lrank} \times \operatorname{Fin}(j+1) \hookrightarrow G$, and for each $j$ and each axis $a$ of degree $j$ that is not short (`AllocatedDegreeActiveAxis (allocatedShortAxis U b S.value) j`, where an axis $(j, \mathrm{inr}\ i)$ is short when `basisAxisScale (b j) i` $= \lceil \|b_{j,i}\|^{-1} \rceil \le \texttt{S.value}^{j+1}$ and axes $(j, \mathrm{inl}\ \cdot)$ are never short) an embedding $\mathrm{block}_{j,a} : \operatorname{Fin} \mathrm{Lrank} \hookrightarrow B_{(j,a)}$. Let $T_{\mathrm{sp}}$ be a finite type, $\mathrm{spatialEquiv} : G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$, $\mathrm{physicalN} : X \to \mathbb{N}$, and $\tau, \delta_{\mathrm{slice}}, P, P_{\mathrm{bad}}, P_{\mathrm{pres}}$ real numbers.
--
--   Let `slice` be an `ActualFixedSpatialSlicedForecastPath` for all these data, with spatial width parameter `allocatedPhysicalRootBudget B U b S (fun _ => 0)` and length parameter `S.value` (a forecast path `slice.path` with base point, integer noise, coefficient sample, read, centers, prime data and reference modulus, together with a common step `slice.step`, kernel progressions of lengths `slice.kernelLength g` and principal progressions with lengths `slice.principalLength`, steps and starts). Let `s` be an `ActualFixedSpatialForecastSetup` for $B, U, b, S, \mathrm{Dmod}$, the selection `allocatedShortIntegerSelection U b S.value` (the inclusion of the short integer axes into pairs $(j, i)$, $i \in \operatorname{Fin} n_j$), $\tau$ and $\delta_{\mathrm{slice}}$ (a bundle of real budgets `s.P`, `s.L`, `s.κ`, … with their positivity facts). Assume the integer span of $b_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$ (hb). Let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, and $bW_j$ a $\mathbb{Z}$-basis, indexed by $E^{\mathrm{out}}_j$, of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`). Let $\mathrm{periodCap}, \mathrm{coverCap}$ be reals, $\mathrm{Lip} \ge 0$, and $W$ a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip` (a modulus at most periodCap, a cover at most coverCap, a mask of norm at most $1$, and a $\mathrm{Lip}$-Lipschitz smooth function of norm at most $1$). Let $\mathrm{originalpoly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` (that is, $\mathbb{R}[X] \otimes (J_j \to \mathbb{R})$) with every coefficient in $U_j$ (hmem) and total degree at most $j+1$ (hdegree).
--
--   **Hypotheses.** Let $\xi > 0$ (hξ) and $\mathrm{physicalN}(x) > 0$ for all $x$ (hbox). Assume:
--   - (hframe) `slice.path.noise` lies in `rectangularWeightIndices 0 W' 1`, where $W'$ = `narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN` (indices $G$, `PrincipalTupleIndex B (layerSamplerDegree I n)`);
--   - $t > 0$ (ht), $|\sigma_j| \le t$ for all $j$ (hσbound), $0 < \delta \le 1$ (hδ, hδone);
--   - (hdense) for every non-short axis $a$ and every $p \in B_a \times \operatorname{Fin}(\deg a)$ (with $\deg (j, \cdot) = j+1$), $\delta \cdot \texttt{S.value}$ is at most the cardinality of `integerProgressionSupport (slice.principalStart ⟨a,p⟩) slice.step (slice.principalLength ⟨a,p⟩)` (the progression of that length, start and step);
--   - $q$ is a positive natural number with $W.\mathrm{modulus} \mid q$ (hperiod), $W.\mathrm{cover} \mid q$ (hcover), $q \mid$ `slice.path.referenceModulus` (hqN);
--   - for every $g \in G$: $q \le$ `slice.kernelLength g` (hsizeG) and $c_0 \cdot q / \texttt{slice.kernelLength g} < 1$ (hsmallG), where $c_0$ = `scalarCubeGridBoundaryConstant Empty`;
--   - for every non-short axis $a$ and $p$ as above: $q \le$ `slice.principalLength ⟨a,p⟩` (hsize) and $c_0 \cdot q / \texttt{slice.principalLength ⟨a,p⟩} < 1$ (hsmall);
--   - $\varepsilon \ge 0$ (hε), $\texttt{slice.step}/\texttt{S.value} \le \varepsilon$ (hmesh), $\eta > 0$ (hη);
--   - (htail) $|t| \cdot$ `polynomialMassC2Budget N₁ m 1` $\le$ `slicedPrincipalC2Tolerance N₁ N₂ m 1 (unitProfilePrincipalLowerBound B) (δ/2) s.L η`, where $N_1$ is the number of pairs $(a, p)$ with $a$ a non-short axis and $p \in B_a \times \operatorname{Fin}(\deg a)$, and $N_2$ the number of non-short axes;
--   - each `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` is a $\mathbb{Z}$-lattice in `euclideanSubspace (U j)` (hlattice); $\nu_j$ is a left-invariant probability measure on the quotient of `euclideanSubspace (U j)` by that lattice; the space `EuclideanJetLayers U (fun _ => Unit)` (the product over $j$ of these quotient tori) is compact (hcompact);
--   - $2 \cdot \texttt{spatialTrimMargin τ physicalN i} \le \mathrm{physicalN}(i)$ for all $i$, where `spatialTrimMargin τ physicalN i` $= \lceil \tau\, \mathrm{physicalN}(i)/4 \rceil$ (hmargin), and `slice.path.base` lies in `trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN)` (the box $\prod_i [r_i, \mathrm{physicalN}(i) - r_i)$ of integers, $r_i$ the margin) (htrimbase);
--   - `data` is an `ActualForecastData physicalN originalpoly Pnative massLog capLog Edata` (a target function on `integerBox physicalN`, center constants, and a finite combination of normalized polynomial twists with coefficient mass at most $e^{\mathrm{massLog}}$ approximating the target within $e^{-\mathrm{Edata}}$), with `data.centerConstant j` equal to (the underlying vector of) `slice.path.center j` (hcenter);
--   - (hκ) `s.κ` equals `forecastGeometricJacobian U b R S.value V τ`, where $V$ is the product over the short integer axes $(j, i)$ of `basisAxisScale (b j) i`;
--   - (hUniversal) for every family of polynomials $\mathrm{poly}_j \in$ `VectorPolynomial X ℝ (J j → ℝ)` with all coefficients in $U_j$ and every $u : X \to \mathbb{Z}$,
--   $\bigl\| \texttt{slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ}\ u - \sum_i \texttt{data.coefficient}\ i \cdot (\texttt{data.twists}\ i).\mathrm{eval}\ \mathrm{physicalN}\ (j \mapsto \mathrm{poly}_j - \texttt{data.centerConstant}\ j)\ u \bigr\| \le e^{-\mathrm{Edata}}$ (here subtracting a constant means `subtractConstant`, i.e. subtracting it from the constant coefficient);
--   - $P_{\mathrm{test}} \ge 0$, $\mathrm{Lip} \le e^{P_{\mathrm{test}}}$, $\mathrm{periodCap} \le e^{P_{\mathrm{test}}}$, $\mathrm{coverCap} \le e^{P_{\mathrm{test}}}$ (hPtest, hLw, hpw, hcw), and $E_{\mathrm{prec}} \ge 0$ (hEprec);
--   - with $A$ = `nativeForecastAmbientExponent m` (a natural number fixed by OpenAI) and $Q = \max(\max(\texttt{s.P}, 2 \max(P_{\mathrm{test}}, 3 P_{\mathrm{native}} + 3) + 1), E_{\mathrm{prec}})$: $e^{(Q + A)^A} \le \mathrm{physicalN}(i)$ for all $i$ (hlarge) and $e^{(Q+A)^A} \le R_{\mathrm{rank}}$ (hRrank);
--   - (hrank) for every $j$, `HasLayerSamplingRank (j+1) physicalN Rrank (U j) (originalpoly j)` holds (OpenAI's condition that no integer row combination of height at most $R_{\mathrm{rank}}$ that is nonzero on $U_j$ makes the degree-$(j+1)$ homogeneous part of $\mathrm{originalpoly}_j$ admit a rational approximation at scales $\mathrm{physicalN}$ and height $R_{\mathrm{rank}}$);
--   - $\mathrm{cutoff}$ is a positive natural number (hcutoff), $0 \le \delta_{\mathrm{grid}} \le 1$ (hδgrid, hδgrid1), and $q \cdot \mathrm{cutoff} / $ `forecastJointGridScale U b R S.value physicalN τ j` $\le \delta_{\mathrm{grid}}$ for every index $j$ of that scale (hgridmesh);
--   - $C$ is a real number, `center` a point of the coefficient torus `CoefficientTorus U`, and `sampleFn`, `readFn` functions of the integer noise; (hglobal) `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center slice.path.center slice.path.base sampleFn readFn` holds (OpenAI's condition that at every noise value the read recovers the noise and, where the centered joint density is nonzero, the sample and read recover the centered conditional polynomial's coefficient data and a rank certificate);
--   - (hz) `allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem center slice.path.base slice.path.noise` $\ne 0$; (hsampleAt) `sampleFn slice.path.noise = slice.path.sample`; (hreadAt) `readFn slice.path.noise = slice.path.read`;
--   - (hfinite) `integerBox physicalN` $= \prod_x [0, \mathrm{physicalN}(x)) \cap \mathbb{Z}^X$ is nonempty; (htarget) `data.target` equals `slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ`.
--
--   **Conclusion.** Then
--   $$\Bigl\| \texttt{slice.nativeMean s W originalpoly} - \frac{1}{\#\,\texttt{integerBox physicalN}} \sum_{u \in \texttt{integerBox physicalN}} W.\mathrm{eval}\ \mathrm{physicalN}\ \bigl(j \mapsto \mathrm{originalpoly}_j - \texttt{data.centerConstant}\ j\bigr)\ u \cdot \texttt{data.target}\ u \Bigr\| \le \mathcal{E},$$
--   where `slice.nativeMean s W originalpoly` is OpenAI's sliced native evaluation mean of $W$ along the path, the second term is the complex mean of the displayed function under the uniform probability weights on `integerBox physicalN`, and $\mathcal{E}$ = `slice.comparisonError` with parameters $\mathrm{Lip}, \xi, t, \delta, \varepsilon, \eta, q, o$, $\delta_{\mathrm{native}} = e^{-\mathrm{Edata}}$, $M = e^{\mathrm{massLog}}$, $E_{\mathrm{prec}}$, $\mathrm{cutoff}$, $\delta_{\mathrm{grid}}$ (the sum of OpenAI's sliced physical comparison error, $2\delta_{\mathrm{native}} + M e^{-E_{\mathrm{prec}}}$, and OpenAI's sliced physical ambient grid error).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison` (in `lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/ActualFixedSpatialSlicedDataComparison.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialSlicedForecastPath.native_ambient_model_comparison)

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

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : slice.path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (slice.path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Eprec Rrank : ℝ} (hEprec : 0 ≤ Eprec)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
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

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail ν hlattice hcompact hmargin htrimbase
  hcenter hκ hUniversal hPtest hLw hpw hcw hEprec hlarge hRrank hrank hcutoff hδgrid
  hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt hfinite htarget in

theorem native_ambient_model_comparison_s2 :
    ‖slice.nativeMean s W originalpoly -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      slice.comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := Real.exp (-Edata)) (M := Real.exp massLog)
        (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  sorry

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
