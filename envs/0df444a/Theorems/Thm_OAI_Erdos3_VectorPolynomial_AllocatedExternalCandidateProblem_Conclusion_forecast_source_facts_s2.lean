-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_forecast_source_facts_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:03.804625+00:00
-- url     : https://prove2.me/theorems/b7a224ca-8fa3-4ba8-8526-d78a29ab820a
-- title:
--   A forecast path read off a retained point of an external candidate conclusion satisfies the frame, trim, density and sample-read facts
-- statement:
--   This statement lives inside OpenAI's sampler framework; every named structure or function below is defined by OpenAI.
--
--   **Data.** Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$, $E^{\mathrm{out}}_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals with proofs `hR`, `hσ` that $R_j > 0$ and $\sigma_j > 0$, and $S$ a `LayerSamplerScale B U b R σ`. Let $X$ be a finite type with decidable equality, $D_{\mathrm{mod}}, L_{\mathrm{rank}}$ natural numbers, `spatial`, `kernel`, `block` the embeddings into $G$ and into the $B_{(j,a)}$ for the allocated degree-active axes, $T_{\mathrm{sp}}$ a type and `spatialEquiv` an equivalence $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$. Let `physicalN : X → ℕ`, reals $\tau$, `cost`, $\delta_{\mathrm{base}}$, $P^{\mathrm{base}}_{\mathrm{pres}}$, $\xi$; `s` an `ActualFixedSpatialForecastSetup` with selection `allocatedShortIntegerSelection U b S.value`, parameter $\tau$ and threshold $e^{-\mathrm{cost}}/2$; and `path` an `ActualFixedSpatialForecastPath` for these data, with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, scale `S.value`, `physicalN`, $\tau$, $\delta_{\mathrm{base}}$, `s.P`, `s.Pbad`, $P^{\mathrm{base}}_{\mathrm{pres}}$.
--
--   Let `hb` be a proof that for each $j$ the $\mathbb{Z}$-span of the range of $b_j$ is the `projectedIntegerLattice` of the Euclidean copy of $U_j$; $o_j$ an orthonormal basis (indexed by $I_j$) of the Euclidean copy of $U_j$; `bW j` a $\mathbb{Z}$-basis, indexed by $E^{\mathrm{out}}_j$, of the `latticeSection` of the standard lattice $\mathbb{Z}^{J_j}$ in that subspace; `originalpoly j` vector polynomials in the variables $X$ with values in $\mathbb{R}^{J_j}$, with `hmem` a proof that all their coefficients lie in $U_j$; $C$ a real number; `center` a point of the `CoefficientTorus`; `sampleFn` and `readFn` functions on integer arrays indexed by `Option (LayerSamplerVariables G I n B) × X`. Let $A$ be an `AllocatedExternalCandidateSampler B U b S hb o hR hσ physicalN originalpoly hmem τ ξ stride cells center` (for some `stride : X → ℕ` and finite set `cells` of column residue patterns); let $L, M$ be $\mathbb{Q}$-Lie algebras, $D$ a `RationalFilteredNilmanifold L r d`, `Fmark` a nilpotent Lie filtration of $M$, $\varphi : L \to M$ a Lie homomorphism, `marked` a polynomial orbit, `observable`, `weight` functions and reals `chartCost`, `massThreshold`, `scoreThreshold`, and $P$ an `AllocatedExternalCandidateProblem A D Fmark φ marked observable weight chartCost massThreshold scoreThreshold`. Let `out` be a `P.Conclusion cost outputMass outputScore` (for reals `outputMass`, `outputScore`) and $z$ an element of `out.retained`, so that $z$ is a pair whose first component is a base point and whose second component is a noise array.
--
--   **Hypotheses.**
--   - `hlattice`: for each $j$, the `latticeSection` of the standard lattice $\mathbb{Z}^{J_j}$ in the Euclidean copy of $U_j$ is a full-rank $\mathbb{Z}$-lattice (`IsZLattice ℝ`).
--   - `hglobal`: `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center path.center path.base sampleFn readFn` holds (for every noise array $w$, `readFn w` recovers the noise $w$, and, whenever `allocatedCenteredJointDensity … center path.base w` is nonzero, the sample `sampleFn w` has the listed recovery properties).
--   - `hbase`: `path.base` is the first component of $z$; `hnoise`: `path.noise` is the second component of $z$.
--   - `hsample`: `path.sample = sampleFn` (second component of $z$).
--   - `hread`: `path.read = allocatedReplaceReadNoise B w (allocatedJointFrameRead a (readFn w))`, where $a$ and $w$ are the first and second components of $z$.
--
--   **Conclusion.** All of the following hold:
--   - `path.noise` lies in `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1`;
--   - `path.base` lies in `trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN)`;
--   - `allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem center path.base path.noise` $\ne 0$;
--   - `sampleFn path.noise = path.sample`;
--   - `readFn path.noise = path.read`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateForecastComparisonSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B301`, `OAIE3v2B233` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateForecastComparisonSource.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecast_source_facts)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B301
import Definitions.Def_OAIE3v2B233

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)

namespace AllocatedExternalCandidateProblem.Conclusion

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
variable (ξ : ℝ)

variable {E Ptest : ℝ}
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
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

variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hEdata : E + 8 ≤ qLate.E)

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)

variable (hprimes : path.primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
variable (hexponent : path.exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)

variable {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ physicalN originalpoly hmem
      τ ξ stride cells center)
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {r d t : ℕ} {D : RationalFilteredNilmanifold L r d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {chartCost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := Eout) A D Fmark φ marked observable weight
      chartCost massThreshold scoreThreshold}
    {outputMass outputScore : ℝ}
    (out : P.Conclusion cost outputMass outputScore)
    (z : out.retained)
    (hkeep : ∀ k, (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔
      qnum.Hchild ≤ A.sides k)
    (hkernel : Nonempty G)
    (hcutoff : qnum.Hchild ≤ S.value)
    (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
    (hdensity : qnum.δ ≤ Real.exp (-cost))
    (hlog : cost + 1 ≤ qnum.v)
    (hprescribed : cost + 1 ≤ s.Ppres)
    (hstride : 2 * Real.exp cost ≤ qnum.Ptail)
    (hbase : path.base = z.val.1.val)
    (hnoise : path.noise = z.val.2.val)
    (hsample : path.sample = sampleFn z.val.2.val)
    (hread : path.read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z.val.2.val)))

include hglobal hbase hnoise hsample hread in
omit [Fintype Tsp] hcompact in
theorem forecast_source_facts_s2 :
    path.noise ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1 ∧
    path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN) ∧
    allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
      center path.base path.noise ≠ 0 ∧
    sampleFn path.noise = path.sample ∧ readFn path.noise = path.read := by
  sorry

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end
