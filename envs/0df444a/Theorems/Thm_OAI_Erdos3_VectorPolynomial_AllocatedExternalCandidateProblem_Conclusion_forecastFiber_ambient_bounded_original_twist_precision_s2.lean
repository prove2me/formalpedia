-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_forecastFiber_ambient_bounded_original_twist_precision_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:15.449861+00:00
-- url     : https://prove2.me/theorems/db868a9b-29ec-45e3-b054-82d67c158102
-- title:
--   A retained path's dense fiber twist mean matches the ambient mean against the early target
-- statement:
--   Work in OpenAI's layer-sampler setting, with the following implicit: a natural number $m$; finite types $G$, $I_j$, $J_j$, $B_a$ and natural numbers $n_j$; subspaces $U_j\subseteq\mathbb{R}^{J_j}$ and bases $b_j$ of the orthogonal complements of `euclideanSubspace (U j)`; reals $R_j>0$, $\sigma_j>0$ (proofs $hR$, $h\sigma$) and a `LayerSamplerScale` $S$; a finite type $X$ with decidable equality; finite types $E^{\mathrm{out}}_j$; natural numbers $D_{\mathrm{mod}},L_{\mathrm{rank}}$; embeddings $\mathrm{spatial}$, $\mathrm{kernel}_j$, $\mathrm{block}_{j,a}$; a finite type $T_{\mathrm{sp}}$ with an equivalence $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; $\mathrm{physicalN}:X\to\mathbb{N}$; reals $\tau,\mathrm{cost},\delta_{\mathrm{base}},P_{\mathrm{presBase}},\mathrm{periodCap},\mathrm{coverCap},E,P_{\mathrm{test}},R_{\mathrm{rank}}$ and $\mathrm{Lip}\ge0$. The section data used are: $s$, an `ActualFixedSpatialForecastSetup` with selection `allocatedShortIntegerSelection U b S.value`, tolerance $\tau$ and slice width $e^{-\mathrm{cost}}/2$; `ActualFixedSpatialSlicedForecastNumerics s` $q_{\mathrm{num}}$ (implicit) and $q_{\mathrm{Late}}$ with equal $\delta$, $H_{\mathrm{child}}$, $v$ and $P_{\mathrm{tail}}$; $\mathrm{path}$, an `ActualFixedSpatialForecastPath` with root budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, scale $S.\mathrm{value}$ and parameters $\tau,\delta_{\mathrm{base}},s.P,s.P_{\mathrm{bad}},P_{\mathrm{presBase}}$; $hb$, the hypothesis that for each $j$ the $\mathbb{Z}$-span of the basis $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` (the orthogonal projection of the standard integer lattice $\mathbb{Z}^{J_j}$ onto the orthogonal complement of `euclideanSubspace (U j)`); orthonormal bases $o_j$; $\mathbb{Z}$-bases $bW_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (assumed a $\mathbb{Z}$-lattice); $W$ a `NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip`; vector polynomials $\mathrm{originalpoly}_j$ with coefficients in $U_j$ ($\mathrm{hmem}$) and degree at most $j+1$; a real $\xi$; left-invariant probability measures $\nu_j$ on the quotient tori, with `EuclideanJetLayers U (fun _ => Unit)` compact; a real $C$, an implicit center of `CoefficientTorus U`, implicit maps $\mathrm{sampleFn},\mathrm{readFn}$; $\mathrm{earlyData}$, an `ActualForecastData physicalN originalpoly …` (a structure bundling a complex target on `integerBox physicalN`, center constants and a twist approximation); implicit $\mathrm{stride}$ and $\mathrm{cells}$; $A$, an `AllocatedExternalCandidateSampler B U b S hb o hR hσ physicalN originalpoly hmem τ ξ stride cells center`; implicit Lie-theoretic data and an `AllocatedExternalCandidateProblem A …` named $P$; $\mathrm{out}$, a `P.Conclusion cost outputMass outputScore`; and a retained path $z$ of $\mathrm{out}$, whose two components are an integer base point and an integer noise array. The hypotheses used are: $|\sigma_j|\le e^{-\phi}$ with $\phi$ = `fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) (2Pu + (E + 4) + 14) m` and $P_u$ = `s.slicedComparisonSourceLog Ptest`; $2\cdot$`spatialTrimMargin τ physicalN i` $\le\mathrm{physicalN}_i$; $s.\kappa$ equals `forecastGeometricJacobian U b R S.value (∏ a, basisAxisScale …) τ`; $P_{\mathrm{test}}\ge0$ and $\mathrm{Lip},\mathrm{periodCap},\mathrm{coverCap}\le e^{P_{\mathrm{test}}}$; $q_{\mathrm{Late}}.\mathrm{massLog}+E+8\ge0$; with $\Lambda=\big(\max(\max(s.P,2\max(P_{\mathrm{test}},3q_{\mathrm{Late}}.P_{\mathrm{native}}+3)+1),q_{\mathrm{Late}}.\mathrm{massLog}+E+8)+e\big)^{e}$ and $e$ = `nativeForecastAmbientExponent m`, $e^{\Lambda}\le\mathrm{physicalN}_i$ for all $i$ and $e^{\Lambda}\le R_{\mathrm{rank}}$; each $\mathrm{originalpoly}_j$ has `HasLayerSamplingRank (j+1) physicalN Rrank (U j)`; `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ originalpoly hmem (allocatedShortAxis U b S.value) spatial kernel block C center path.center path.base sampleFn readFn`; $\mathrm{cost}\ge0$, $E\ge0$, $\tau\le1$; `comparisonPrecisionFloor s (Dmod + |Σ j, I j|) Pu (2Ptest) E` $\le S.\mathrm{value}$; $\xi\le e^{-(2P_u+(E+4)+14)}$; $E+8\le q_{\mathrm{Late}}.E$; $\exp$(`forecastJointGridAmbientLog (Dmod + |Σ j, I j|) (comparisonGridLog s Pu) (E + 4) (2Ptest) s.Pτ`) $\le\mathrm{physicalN}_i$ for all $i$; $\mathrm{earlyData.centerConstant}_j=\mathrm{path.center}_j$; $\mathrm{path.primes}$ = `boundedPrimes ⌈exp (2Ptest)⌉₊` and $\mathrm{path.exponent}(p)=$ `Nat.log p ⌈exp (2Ptest)⌉₊`; $\mathrm{path.base}$ and $\mathrm{path.noise}$ are the two components of $z$; $\mathrm{path.sample}=\mathrm{sampleFn}(\text{noise of }z)$; and $\mathrm{path.read}$ = `allocatedReplaceReadNoise B (noise of z) (allocatedJointFrameRead (base of z) (readFn (noise of z)))`. (The section hypotheses `hkeep`, `hkernel`, `hcutoff`, `hlate`, `hdensity`, `hlog`, `hprescribed`, `hstride` are not part of this statement.)
--
--   The theorem takes $\mathrm{input}$, an `ActualFixedSpatialDenseSliceInput s qnum` with $\mathrm{input.cost}=\mathrm{cost}$, and assumes that $\mathrm{earlyData.target}$ equals `(path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ`. Conclusion:
--   $$\Big\|\,\mathbb{E}_{\mathrm{site}\sim\mathrm{fib}}\,W.\mathrm{eval}\big(\mathrm{physicalN},\mathrm{originalpoly},\,a\mapsto\mathrm{path.base}(a)+\text{integerPhysicalSite}(\mathrm{site},\mathrm{path.noise})(a)\big)\;-\;\mathbb{E}_{u}\,W.\mathrm{eval}(\mathrm{physicalN},\mathrm{originalpoly},u)\cdot\mathrm{earlyData.target}(u)\Big\|\le e^{-E},$$
--   where $\mathrm{fib}$ is `input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside`, the second mean is over the uniform law on `integerBox physicalN` (nonempty by `A.integerBox_nonempty`), and both are `complexMean`s.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateForecastComparisonSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateForecastComparisonSource.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.forecastFiber_ambient_bounded_original_twist_precision)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266

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
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
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
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
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

variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) (2 * Ptest) s.Pτ) ≤ (physicalN i : ℝ))

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

include hR hσ hdegree hσbound ν hlattice hcompact hmargin hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hcost hE hτ1 hfloor hξsmall hEdata hNgrid
  hEarlyCenter hδlate hHlate hvlate hTaillate hprimes hexponent
  hbase hnoise hsample hread in

theorem forecastFiber_ambient_bounded_original_twist_precision_s2
    (input : ActualFixedSpatialDenseSliceInput s qnum)
    (hcost_match : input.cost = cost)
    (hTarget : earlyData.target = (path.toDenseSliceMember input).slice.target
      (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ) :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun site => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite site.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) A.integerBox_nonempty).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  sorry

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end
