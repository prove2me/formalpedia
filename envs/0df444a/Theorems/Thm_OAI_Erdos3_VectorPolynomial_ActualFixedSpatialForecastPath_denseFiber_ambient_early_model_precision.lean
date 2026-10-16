-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_denseFiber_ambient_early_model_precision
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_early_model_precision
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:27:27.782549+00:00
-- url     : https://prove2.me/theorems/99680ce0-bf4b-49c0-8bcf-a2aa0da41566
-- title:
--   A dense fiber mean of a twist matches its ambient mean against the early model target
-- statement:
--   Work in OpenAI's layer-sampler setting, with the following implicit: a natural number $m$; finite types $G$, $I_j$, $J_j$, $B_a$ and natural numbers $n_j$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ (proofs $hR$, $h\sigma$) and a `LayerSamplerScale` $S$; a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}},L_{\mathrm{rank}}$; embeddings $\mathrm{spatial}$, $\mathrm{kernel}_j$, $\mathrm{block}_{j,a}$; a finite type $T_{\mathrm{sp}}$ with an equivalence $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; $\mathrm{physicalN}:X\to\mathbb{N}$; reals $\tau,\mathrm{cost},\delta_{\mathrm{base}},P_{\mathrm{presBase}},\mathrm{periodCap},\mathrm{coverCap},V,E,P_{\mathrm{test}},R_{\mathrm{rank}}$ and $\mathrm{Lip}\ge0$. The data are: $s$, an `ActualFixedSpatialForecastSetup` with selection `allocatedShortIntegerSelection U b S.value`, tolerance $\tau$ and slice width $e^{-\mathrm{cost}}/2$; an implicit `ActualFixedSpatialSlicedForecastNumerics s` $q_{\mathrm{num}}$; $\mathrm{path}$, an `ActualFixedSpatialForecastPath` with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, scale $S.\mathrm{value}$ and parameters $\tau,\delta_{\mathrm{base}},s.P,s.P_{\mathrm{bad}},P_{\mathrm{presBase}}$; $\mathrm{input}$, an `ActualFixedSpatialDenseSliceInput s qnum` with $\mathrm{input.cost}=\mathrm{cost}$; $hb$ (the $\mathbb{Z}$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`); orthonormal bases $o_j$ of `euclideanSubspace (U j)`; $\mathbb{Z}$-bases $bW_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`, assumed a $\mathbb{Z}$-lattice; $W$ a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip`; vector polynomials $\mathrm{originalpoly}_j$ with coefficients in $U_j$ ($\mathrm{hmem}$) and degree at most $j+1$; a real $\xi>0$; a nonzero natural number $q$ with $W.\mathrm{modulus}\mid q$, $W.\mathrm{cover}\mid q$, $q\mid$ `path.referenceModulus` and $q\le e^{V}$; left-invariant probability measures $\nu_j$ on the quotient tori, with `EuclideanJetLayers U (fun _ => Unit)` compact; a real $C$, an implicit center of `CoefficientTorus U`, and implicit maps $\mathrm{sampleFn},\mathrm{readFn}$ from integer noise arrays to coefficient samples and read-outs; and two `ActualForecastData physicalN originalpoly …` structures $\mathrm{lateData}$ (with parameters $P^{\mathrm{late}}_{\mathrm{native}},\mathrm{lateMassLog},\mathrm{lateCapLog},\mathrm{lateEdata}$) and $\mathrm{earlyData}$ (each bundles a complex target on `integerBox physicalN`, center constants, and a finite combination of normalized twists with complex coefficients approximating the target). The hypotheses are: $\mathrm{physicalN}_x>0$ for all $x$; $\mathrm{path.noise}$ lies in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths … τ ξ physicalN) 1`; $|\sigma_j|\le e^{-\phi}$ with $\phi$ = `fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) (2Pu + (E + 4) + 14) m` and $P_u$ = `s.slicedComparisonSourceLog Ptest`; $2\cdot$`spatialTrimMargin τ physicalN i` $\le\mathrm{physicalN}_i$; $\mathrm{path.base}\in$ `trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN)`; $\mathrm{lateData.centerConstant}_j=\mathrm{path.center}_j$; $s.\kappa$ equals `forecastGeometricJacobian U b R S.value (∏ a, basisAxisScale …) τ`; for every family of vector polynomials $\mathrm{poly}_j$ with coefficients in $U_j$ and every $u:X\to\mathbb{Z}$, $\|$`(path.toDenseSliceMember input).slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u` $-\sum_i \mathrm{lateData.coefficient}_i\cdot(\mathrm{lateData.twists}_i).\mathrm{eval}(\mathrm{physicalN},\ j\mapsto\mathrm{poly}_j-\mathrm{lateData.centerConstant}_j,\ u)\|\le e^{-\mathrm{lateEdata}}$; $P_{\mathrm{test}}\ge0$ and $\mathrm{Lip},\mathrm{periodCap},\mathrm{coverCap}\le e^{P_{\mathrm{test}}}$; $\mathrm{lateMassLog}+E+8\ge0$; with $\Lambda=\big(\max(\max(s.P,2\max(P_{\mathrm{test}},3P^{\mathrm{late}}_{\mathrm{native}}+3)+1),\mathrm{lateMassLog}+E+8)+e\big)^{e}$ and $e$ = `nativeForecastAmbientExponent m`, $e^{\Lambda}\le\mathrm{physicalN}_i$ for all $i$ and $e^{\Lambda}\le R_{\mathrm{rank}}$; each $\mathrm{originalpoly}_j$ has `HasLayerSamplingRank (j+1) physicalN Rrank (U j)`; `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center path.center path.base sampleFn readFn`; `allocatedCenteredJointDensity … center path.base path.noise` $\ne0$; $\mathrm{sampleFn}(\mathrm{path.noise})=\mathrm{path.sample}$ and $\mathrm{readFn}(\mathrm{path.noise})=\mathrm{path.read}$; $\mathrm{hfinite}$: `integerBox physicalN` is nonempty; $\mathrm{lateData.target}$ equals `(path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ`; $\mathrm{cost}\ge0$, $E\ge0$, $\tau\le1$; `comparisonPrecisionFloor s (Dmod + |Σ j, I j|) Pu V E` $\le S.\mathrm{value}$; $\xi\le e^{-(2P_u+(E+4)+14)}$; $E+8\le\mathrm{lateEdata}$; $\exp$(`forecastJointGridAmbientLog (Dmod + |Σ j, I j|) (comparisonGridLog s Pu) (E + 4) V s.Pτ`) $\le\mathrm{physicalN}_i$ for all $i$; $\mathrm{earlyData.centerConstant}_j=\mathrm{path.center}_j$; and $\mathrm{earlyData.target}$ equals the same slice target as $\mathrm{lateData.target}$. Conclusion:
--   $$\Big\|\,\mathbb{E}_{z\sim\mathrm{fib}}\,W.\mathrm{eval}\big(\mathrm{physicalN},\mathrm{path.physicalPolynomial}(\mathrm{originalpoly}),\,a\mapsto\mathrm{path.base}(a)+\text{integerPhysicalSite}(z,\mathrm{path.noise})(a)\big)\;-\;\mathbb{E}_{u}\,W.\mathrm{eval}\big(\mathrm{physicalN},\,j\mapsto\mathrm{originalpoly}_j-\mathrm{earlyData.centerConstant}_j,\,u\big)\cdot\mathrm{earlyData.target}(u)\Big\|\le e^{-E},$$
--   where $\mathrm{fib}$ is `input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside`, `path.physicalPolynomial` and "$-$ constant" are `subtractConstant` (subtracting the constant vector from the polynomial), the second mean is over the uniform law on `integerBox physicalN`, and both are `complexMean`s.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_early_model_precision` in `lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B079` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean#L701

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B079

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

variable (hactive : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val), keep (Sum.inr ⟨j.1.val, j.2⟩))

variable {X : Type*} [Fintype X]
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hkernelLength : ∀ g, 2 ≤ slice.length ⟨Sum.inl g, hkernel g⟩)
variable (hactiveLength : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val),
  2 ≤ slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))

section ActualChild

variable {Hcut : ℕ} (hHcut : Hcut ≤ S.value)
variable (child : ResidueBoxSlice
  (fun k : {k : LayerSamplerVariables G I n B //
    Hcut ≤ Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hq : 0 < q) {cost : ℝ} (hlarge : 2 * Real.exp cost ≤ (S.value : ℝ))
variable (hfraction : ∀ k, Real.exp (-cost) *
  ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℝ) ≤
    child.length k)

variable (hchildlen : ∀ k, 0 < child.length k)
variable (fixedChild : {k : LayerSamplerVariables G I n B //
  ¬Hcut ≤ Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k} → ℤ)
variable (hfixedChild : ∀ k, 0 ≤ fixedChild k ∧ fixedChild k <
  ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))

end ActualChild
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ δslice δbase PpresBase : ℝ}
variable {s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice}
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ)
  physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

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

namespace ActualFixedSpatialForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (num : ActualFixedSpatialSlicedForecastNumerics s)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ)
  physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s num)

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
variable (hframe : ((path.toDenseSliceMember input).slice).path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (((path.toDenseSliceMember input).slice).principalStart ⟨a.val,p⟩) (((path.toDenseSliceMember input).slice).step : ℤ)
      (((path.toDenseSliceMember input).slice).principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ ((path.toDenseSliceMember input).slice).path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ ((path.toDenseSliceMember input).slice).kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / ((path.toDenseSliceMember input).slice).kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ ((path.toDenseSliceMember input).slice).principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / ((path.toDenseSliceMember input).slice).principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (((path.toDenseSliceMember input).slice).step : ℝ) / S.value ≤ ε)
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
variable (htrimbase : ((path.toDenseSliceMember input).slice).path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (((path.toDenseSliceMember input).slice).path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value ((∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ))) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((path.toDenseSliceMember input).slice).targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
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
  center ((path.toDenseSliceMember input).slice).path.center ((path.toDenseSliceMember input).slice).path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center ((path.toDenseSliceMember input).slice).path.base ((path.toDenseSliceMember input).slice).path.noise ≠ 0)
variable (hsampleAt : sampleFn ((path.toDenseSliceMember input).slice).path.noise = ((path.toDenseSliceMember input).slice).path.sample)
variable (hreadAt : readFn ((path.toDenseSliceMember input).slice).path.noise = ((path.toDenseSliceMember input).slice).path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = ((path.toDenseSliceMember input).slice).target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

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
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖(path.toDenseSliceMember input).slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ Edata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

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
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {latePnative lateMassLog lateCapLog lateEdata : ℝ}
variable (lateData : ActualForecastData physicalN originalpoly latePnative lateMassLog lateCapLog lateEdata)
variable (hLateCenter : lateData.centerConstant = fun j => (path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖(path.toDenseSliceMember input).slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, lateData.coefficient i * (lateData.twists i).eval physicalN
      (fun j => subtractConstant (lateData.centerConstant j) (poly j)) u‖ ≤ Real.exp (-lateEdata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ lateMassLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * latePnative + 3) + 1)) (lateMassLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * latePnative + 3) + 1)) (lateMassLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hLateTarget : lateData.target = (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ lateEdata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hLateCenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite hLateTarget
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget in
theorem denseFiber_ambient_early_model_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (earlyData.centerConstant j) (originalpoly j)) u.val *
            earlyData.target u)‖ ≤ Real.exp (-E) := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial
end
end OAI
