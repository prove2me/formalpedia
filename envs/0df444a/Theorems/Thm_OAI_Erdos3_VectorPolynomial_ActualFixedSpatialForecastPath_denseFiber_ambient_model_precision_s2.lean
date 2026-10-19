-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_ActualFixedSpatialForecastPath_denseFiber_ambient_model_precision_s2
-- name    : OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:54:22.584908+00:00
-- url     : https://prove2.me/theorems/e7e6bd53-167a-443a-8efc-48915b990682
-- title:
--   On a fixed spatial forecast path, the dense fiber mean of a polynomial twist matches the ambient model mean to precision exp(-E)
-- statement:
--   This statement lives inside a large context of parameters (the `variable` lines of OpenAI's file); all objects below are those of OpenAI's sampler framework, and every named structure or function is defined by OpenAI.
--
--   **Data.** Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$, $E^{\mathrm{out}}_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals with $R_j > 0$ and $\sigma_j > 0$ (hypotheses `hR`, `hσ`), and $S$ a `LayerSamplerScale B U b R σ`. Let $X$ be a finite type with decidable equality, $D_{\mathrm{mod}}$ and $L_{\mathrm{rank}}$ natural numbers, `spatial` an embedding of $\{0,\dots,L_{\mathrm{rank}}-1\}$ into $G$, `kernel j` embeddings of $\{0,\dots,L_{\mathrm{rank}}-1\} \times \{0,\dots,j\}$ into $G$, `block j a` embeddings of $\{0,\dots,L_{\mathrm{rank}}-1\}$ into $B_{(j,a)}$ for each allocated degree-active axis $a$, $T_{\mathrm{sp}}$ a finite type and `spatialEquiv` an equivalence $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$. Let `physicalN : X → ℕ`, and reals $\tau$, `cost`, $\delta_{\mathrm{base}}$, $P^{\mathrm{base}}_{\mathrm{pres}}$. Let `s` be an `ActualFixedSpatialForecastSetup` for these data with selection `allocatedShortIntegerSelection U b S.value`, parameter $\tau$ and threshold $e^{-\mathrm{cost}}/2$; `qnum` an `ActualFixedSpatialSlicedForecastNumerics s`; `path` an `ActualFixedSpatialForecastPath` for these data with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, scale `S.value`, `physicalN`, $\tau$, $\delta_{\mathrm{base}}$, `s.P`, `s.Pbad`, $P^{\mathrm{base}}_{\mathrm{pres}}$; and `input` an `ActualFixedSpatialDenseSliceInput s qnum`.
--
--   Further let $o_j$ be an orthonormal basis (indexed by $I_j$) of the Euclidean copy of $U_j$; `bW j` a $\mathbb{Z}$-basis, indexed by $E^{\mathrm{out}}_j$, of the `latticeSection` of the standard lattice $\mathbb{Z}^{J_j}$ in that subspace; reals `periodCap`, `coverCap` and a nonnegative real `Lip`; `W` a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip`; vector polynomials `originalpoly j` in the variables $X$ with values in $\mathbb{R}^{J_j}$; reals $\xi$, $V$, $E$, $P_{\mathrm{test}}$, $R_{\mathrm{rank}}$, $C$, $P_{\mathrm{native}}$, `massLog`, `capLog`, $E_{\mathrm{data}}$; a natural number $q \ne 0$; for each $j$ an additively left-invariant probability measure $\nu_j$ on the quotient of the Euclidean copy of $U_j$ by the lattice section; `data` an `ActualForecastData physicalN originalpoly Pnative massLog capLog Edata`; `center` a point of the `CoefficientTorus`; and functions `sampleFn`, `readFn` on integer arrays indexed by `Option (LayerSamplerVariables G I n B) × X`.
--
--   **Hypotheses.**
--   - `hcost_match`: `input.cost` $=$ cost.
--   - `hb`: for each $j$, the $\mathbb{Z}$-span of the range of $b_j$ is the `projectedIntegerLattice` of the Euclidean copy of $U_j$.
--   - `hmem`: every coefficient of `originalpoly j` lies in $U_j$; `hdegree`: `originalpoly j` has degree at most $j+1$ (`DegreeLE` with all variable weights $1$).
--   - `hξ`: $\xi > 0$; `hbox`: `physicalN x` $> 0$ for all $x$.
--   - `hframe`: `path.noise` lies in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1`.
--   - `hσbound`: for all $j$, $|\sigma_j| \le \exp\bigl(-\texttt{fixedPathSlicedPerturbationLog}\ D\ (D + \Sigma + 4)\ (\mathrm{cost}+1)\ (2\Sigma + (E+4) + 14)\ m\bigr)$, where $D$ = `s.D` and $\Sigma$ = `s.slicedComparisonSourceLog Ptest`.
--   - `hperiod`, `hcover`: `W.modulus` and `W.cover` divide $q$; `hqN`: $q$ divides `path.referenceModulus`.
--   - each lattice section is a full-rank $\mathbb{Z}$-lattice (`hlattice`), and the space `EuclideanJetLayers U (fun _ => Unit)` is compact (`hcompact`).
--   - `hmargin`: $2\cdot$ `spatialTrimMargin τ physicalN i` $\le$ `physicalN i` for all $i$; `htrimbase`: `path.base` lies in `trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN)`.
--   - `hcenter`: `data.centerConstant` $= (j \mapsto$ `(path.center j).val`$)$.
--   - `hκ`: `s.κ` equals `forecastGeometricJacobian U b R S.value (∏ a, basisAxisScale …) τ`, the product running over the axes $a$ of `allocatedShortIntegerSelection U b S.value`, of `basisAxisScale` of the corresponding basis vector.
--   - `hUniversal`: for every family of vector polynomials `poly j` with coefficients in $U_j$ and every $u : X \to \mathbb{Z}$,
--   $$\Bigl\|\texttt{targetAt}(\mathrm{poly}, u) - \sum_i \texttt{data.coefficient}\ i \cdot (\texttt{data.twists}\ i).\texttt{eval}\ \mathrm{physicalN}\ \bigl(j \mapsto \texttt{subtractConstant}\ (\texttt{data.centerConstant}\ j)\ (\mathrm{poly}\ j)\bigr)\ u\Bigr\| \le e^{-E_{\mathrm{data}}},$$
--   where `targetAt` is `(path.toDenseSliceMember input).slice.targetAt` with the selection, `s.hBactive`, $o$, `bW`, `hb`, poly, its membership proof and `s.κ`.
--   - `hPtest`: $0 \le P_{\mathrm{test}}$; `hLw`, `hpw`, `hcw`: $\mathrm{Lip} \le e^{P_{\mathrm{test}}}$, $\mathrm{periodCap} \le e^{P_{\mathrm{test}}}$, $\mathrm{coverCap} \le e^{P_{\mathrm{test}}}$.
--   - `hEprec`: $0 \le \mathrm{massLog} + E + 8$.
--   - `hlarge`, `hRrank`: with $K$ = `nativeForecastAmbientExponent m` and $M = \max\bigl(\max(\texttt{s.P},\ 2\max(P_{\mathrm{test}}, 3P_{\mathrm{native}}+3)+1),\ \mathrm{massLog}+E+8\bigr)$, we have $\exp((M+K)^K) \le$ `physicalN i` for all $i$, and $\exp((M+K)^K) \le R_{\mathrm{rank}}$.
--   - `hrank`: for each $j$, `HasLayerSamplingRank (j+1) (physicalN) Rrank (U j) (originalpoly j)`.
--   - `hglobal`: `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center path.center path.base sampleFn readFn`.
--   - `hz`: `allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem center path.base path.noise` $\ne 0$.
--   - `hsampleAt`, `hreadAt`: `sampleFn path.noise = path.sample` and `readFn path.noise = path.read`.
--   - `hfinite`: `integerBox physicalN` (the box $\prod_x [0, \mathrm{physicalN}\ x)$ of integer points) is nonempty.
--   - `htarget`: `data.target` equals `(path.toDenseSliceMember input).slice.target` (with the selection, `s.hBactive`, $o$, `bW`, `hb`, `originalpoly`, `hmem`, `s.κ`).
--   - `hcost`: $0 \le \mathrm{cost}$; `hE`: $0 \le E$; `hτ1`: $\tau \le 1$; `hq`: $q \le e^{V}$.
--   - `hfloor`: `ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + |Σ j, I j|) Σ V E` $\le$ `S.value`.
--   - `hξsmall`: $\xi \le \exp(-(2\Sigma + (E+4) + 14))$; `hEdata`: $E + 8 \le E_{\mathrm{data}}$.
--   - `hNgrid`: for all $i$, $\exp\bigl(\texttt{forecastJointGridAmbientLog}\ (D_{\mathrm{mod}} + |\textstyle\sum_j I_j|)\ (\texttt{comparisonGridLog s}\ \Sigma)\ (E+4)\ V\ \texttt{s.Pτ}\bigr) \le$ `physicalN i`.
--
--   **Conclusion.** Let $\mu$ be the fiber slice law `input.box.fiberSliceLaw` (a finite probability law on the fiber, built from `input.length_pos`, `input.fixed`, `input.fixed_inside`), and $\lambda$ the uniform probability law on `integerBox physicalN`. Then
--   $$\Bigl|\mathbb{E}_{z \sim \mu}\, \texttt{W.eval}\ \mathrm{physicalN}\ (\texttt{path.physicalPolynomial originalpoly})\ \bigl(a \mapsto \texttt{path.base}\ a + \texttt{integerPhysicalSite}\ z\ \texttt{path.noise}\ a\bigr) - \mathbb{E}_{u \sim \lambda}\, \texttt{W.eval}\ \mathrm{physicalN}\ \bigl(j \mapsto \texttt{subtractConstant}\ (\texttt{data.centerConstant}\ j)\ (\texttt{originalpoly}\ j)\bigr)\ u \cdot \texttt{data.target}\ u\Bigr| \le e^{-E}.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision` (in `lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/ActualFiberSlicedBoundedTwistPrecision.lean (declaration OAI.Erdos3.VectorPolynomial.ActualFixedSpatialForecastPath.denseFiber_ambient_model_precision)

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

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hcenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite htarget
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match in

theorem denseFiber_ambient_model_precision_s2 :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      Real.exp (-E) := by
  sorry

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
end
