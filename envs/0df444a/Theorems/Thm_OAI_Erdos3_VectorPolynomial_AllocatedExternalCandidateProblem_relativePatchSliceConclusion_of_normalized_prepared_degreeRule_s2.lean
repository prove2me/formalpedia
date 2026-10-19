-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:06:24.396258+00:00
-- url     : https://prove2.me/theorems/d1b95df4-fb8c-48ae-8b31-fa0c9fe1de96
-- title:
--   A normalized prepared candidate with a degree rule yields a relative patch slice conclusion
-- statement:
--   Setting (section data used by the statement). Let $m$ be a natural number, $G,X,J_0$ types with $G,X$ finite, and $\mathrm{prep}$ a `RankPreparationFamily X J₀ m` (layers with subspaces $(\mathrm{prep}\,j).\mathrm{space}\subseteq\mathbb{R}^{\mathrm{Coord}_j}$, polynomials $(\mathrm{prep}\,j).\mathrm{poly}$ and ranks); let $\mathrm{preparationP}$ be a real and $R_{\mathrm{prep}}$ a natural number (implicit) with `prep.PreparedHeights preparationP Rprep` (each layer valid with OpenAI's explicit heights; it supplies the coefficient-membership proofs written $hm$ in the sampler $A$ below, not to be confused with the hypothesis $m\le\mathrm{degree}$), $\mathrm{preparationP}\ge0$ and $R_{\mathrm{prep}}\ge1$. Implicitly: finite types $I_j$, $E^{\mathrm{out}}_j$, $B_a$ and naturals $n_j$; bases $b_j$ of the orthogonal complements of `euclideanSubspace ((prep j).space)`; reals $R_j>0$, $\sigma_j>0$ ($hR$, $h\sigma$) and a `LayerSamplerScale` $S$; naturals $D_{\mathrm{mod}},L_{\mathrm{rank}}$, embeddings $\mathrm{spatial},\mathrm{kernel}_j,\mathrm{block}_{j,a}$, a finite type $T_{\mathrm{sp}}$ with $G\simeq X\oplus(X\oplus T_{\mathrm{sp}})$; $N:X\to\mathbb{N}$; reals $\tau,\xi,\mathrm{cost}$; $hb$; orthonormal bases $o_j$; $\mathrm{stride}$, $\mathrm{cells}$, a center of the coefficient torus, and $A$, an `AllocatedExternalCandidateSampler B (prep ·).space b S hb o hR hσ N (prep ·).poly hm τ ξ stride cells center` (with path law $A.\mathrm{law}$ and sides $A.\mathrm{sides}$). Explicitly: $s$, an `ActualFixedSpatialForecastSetup` with selection `allocatedShortIntegerSelection`, tolerance $\tau$ and slice width $e^{-\mathrm{cost}}/2$; $q_{\mathrm{num}},q_{\mathrm{Late}}$, two `ActualFixedSpatialSlicedForecastNumerics s`; $\mathbb{Z}$-bases $bW_j$ of `latticeSection (standardEuclideanLattice Coord_j) (euclideanSubspace (prep j).space)` (assumed a $\mathbb{Z}$-lattice); left-invariant probability measures $\nu_j$ on the quotient tori, with `EuclideanJetLayers` compact; a `PolynomialPatch Y degree d` named $\mathrm{patch}$ (type $Y$, naturals $\mathrm{degree},d$ implicit), with `PolynomialShearIndex patch.weight` finite (a `Fintype` instance); $f:\mathbb{Z}^X\to\mathbb{R}$ and $\lambda\in\mathbb{R}$; implicit reals $\mathrm{chartCost},\mathrm{childCost},\mathrm{normBudget},\mathrm{gainLog},\mathrm{gain},p_{\mathrm{Global}}$, naturals $\mathrm{rankBound},\mathrm{netExponent}$, and a finset $\mathrm{productive}$ of paths; $P$, an `AllocatedExternalCandidateProblem A (polynomialShearNilmanifold patch.weight degree patch.weight_le) (RationalTorus.trivialFiltration degree) 0 1 (fun _ z => patch.shearObservable z) (fun x => f x - lam) chartCost μ₀ (exp (-normBudget))` with $\mu_0=\dfrac{A.\mathrm{law.mass}(\mathrm{productive})}{(D'+1)(\mathrm{degree}+1)^{D'}}\,e^{-\mathrm{normBudget}}$, $D'=\min(\mathrm{rankBound},\lfloor\mathrm{childCost}\rfloor)$ (a structure bundling a productive set $P.\mathrm{productive}$ of paths, local charts, a center lift and local candidates); the hypotheses $\mathrm{childCost}\ge0$, $d\le D'$, $\mathrm{childCost}\le\mathrm{normBudget}$, `realPolynomialMass (patch.form.center i)` $\le\mathrm{normBudget}$ for all $i$, $\mathrm{patch.kernel.lip}\le e^{\mathrm{normBudget}}$, $e^{-\mathrm{gainLog}}\le\mathrm{gain}$, $\mathrm{gain}/16<A.\mathrm{law.mass}(\mathrm{productive})$, $(\mathrm{normBudget}+2)^{k}\le p_{\mathrm{Global}}$ with $k$ = `allocatedNormalizedShearObservableExponent degree`, $p_{\mathrm{Global}}\ge0$, $\mathrm{chartCost}\le p_{\mathrm{Global}}$, $\mathrm{normBudget}\le p_{\mathrm{Global}}$, $\mathrm{gainLog}+16+(\mathrm{degree}+1)\mathrm{childCost}+\mathrm{normBudget}\le p_{\mathrm{Global}}$, $f(x)\in[0,1]$ for all $x$, $\lambda\in[0,1]$; $\mathrm{rule}$: `A.DegreeGlobalizationAt (fun x => f x - lam) degree netExponent pGlobal cost` (OpenAI's proposition that every candidate problem with complexity bounds $p_{\mathrm{Global}}$ on a rational filtered nilmanifold of the given degree has a `Conclusion` with cost $\mathrm{cost}$ and mass and score $e^{-\mathrm{cost}}$); for each $z\in P.\mathrm{productive}$ an `ActualFixedSpatialForecastPath` $\mathrm{path}(z)$ (root budget `allocatedPhysicalRootBudget … (fun _ => 0)`, scale $S.\mathrm{value}$, box $N$, parameters $\tau,\delta_{\mathrm{base}},s.P,s.P_{\mathrm{bad}},P_{\mathrm{presBase}}$, with $\delta_{\mathrm{base}},P_{\mathrm{presBase}}$ implicit); and: for each productive $z$ and $k$, the keep-predicate of $P.\mathrm{chart}\,z$ holds iff $q_{\mathrm{num}}.H_{\mathrm{child}}\le A.\mathrm{sides}\,k$; $G$ nonempty; $q_{\mathrm{num}}.H_{\mathrm{child}}\le S.\mathrm{value}$; $2\le e^{-\mathrm{cost}}S.\mathrm{value}$; $q_{\mathrm{num}}.\delta\le e^{-\mathrm{cost}}$; $\mathrm{cost}+1\le q_{\mathrm{num}}.v$; $\mathrm{cost}+1\le s.P_{\mathrm{pres}}$; $2e^{\mathrm{cost}}\le q_{\mathrm{num}}.P_{\mathrm{tail}}$.
--
--   Hypotheses of the theorem: $q_{\mathrm{num}}$ and $q_{\mathrm{Late}}$ have equal $\delta,H_{\mathrm{child}},v,P_{\mathrm{tail}}$; $\xi\le1$; $2\cdot$`spatialTrimMargin τ N x` $\le N_x$; implicit reals $u,p,p_{\mathrm{Slice}},p_{\mathrm{Test}},\mathrm{localBudget},\mathrm{precision},C,E_{\mathrm{compare}},P_{\mathrm{test}},R_{\mathrm{rank}},C_{\mathrm{recovered}}$ with $u,p,\mathrm{localBudget}\ge0$, $p_{\mathrm{Slice}}\,|\mathrm{LayerSamplerVariables}\ G\ I\ n\ B|\le p$, $1\le C\le e^{p}$, $q_{\mathrm{num}}.\mathrm{capLog}\le p$, $2u+4p+12\le q_{\mathrm{num}}.E$, `actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p` $\le\mathrm{precision}$; `A.NativeDetection 0 pSlice pTest localBudget α` with $\alpha$ = `forecastAugmentedUnitThreshold u p (exp (pSlice·|LayerSamplerVariables G I n B|)) C (exp qnum.capLog)`; the `excessMass` of `A.law.siteLaw (A.physicalBox hξone hmargin)` over the uniform law on `integerBox N` at level $C$ is at most $6\,e^{-(2\,\mathrm{precision}+4)}$ (`positiveProjectionAccuracy`); $p_{\mathrm{Slice}}\ge0$, $\mathrm{cost}\le p_{\mathrm{Slice}}$, $\mathrm{chartCost}\le p_{\mathrm{Slice}}$, $p_{\mathrm{Test}}\ge2$, $\sigma_j\le1$; $e:\mathrm{Fin}\,\mathrm{tagCount}\simeq$ `prep.PreparedCoordinate`; $2\,\mathrm{cost}+6\le u$; $\max(\max(\mathrm{localBudget},3q_{\mathrm{num}}.P_{\mathrm{native}}+3),2u+4p+\max(0,q_{\mathrm{num}}.\mathrm{massLog})+20)+2+2\,\mathrm{cost}+8\le E_{\mathrm{compare}}$; $\max(\mathrm{localBudget},3q_{\mathrm{num}}.P_{\mathrm{native}}+3)\le P_{\mathrm{test}}$; $|\sigma_j|\le e^{-\phi}$ with $\phi$ = `fixedPathSlicedPerturbationLog s.D (s.D + Pu + 4) (cost + 1) (2Pu + (Ecompare + 4) + 14) m`, $P_u$ = `s.slicedComparisonSourceLog Ptest`; $s.\kappa$ = `forecastGeometricJacobian … S.value (∏ a, basisAxisScale …) τ`; $q_{\mathrm{Late}}.\mathrm{massLog}+E_{\mathrm{compare}}+8\ge0$; with $\Lambda=\big(\max(\max(s.P,2\max(P_{\mathrm{test}},3q_{\mathrm{Late}}.P_{\mathrm{native}}+3)+1),q_{\mathrm{Late}}.\mathrm{massLog}+E_{\mathrm{compare}}+8)+e'\big)^{e'}$, $e'$ = `nativeForecastAmbientExponent m`: $e^{\Lambda}\le N_i$ and $e^{\Lambda}\le R_{\mathrm{rank}}$; each $(\mathrm{prep}\,j).\mathrm{poly}$ has `HasLayerSamplingRank (j+1) N Rrank`; maps $\mathrm{sampleFn},\mathrm{readFn}$ indexed by productive paths with `AllocatedCenteredRecoveredSampleReadAt … Crecovered center (path z).center (path z).base (sampleFn z) (readFn z)` for every $z$; $\mathrm{cost}\ge0$, $E_{\mathrm{compare}}\ge0$, $\tau\le1$; `comparisonPrecisionFloor s (Dmod + |Σ j, I j|) Pu (2Ptest) Ecompare` $\le S.\mathrm{value}$; $\xi\le e^{-(2P_u+(E_{\mathrm{compare}}+4)+14)}$; $E_{\mathrm{compare}}+8\le q_{\mathrm{Late}}.E$; $\exp$(`forecastJointGridAmbientLog (Dmod + |Σ j, I j|) (comparisonGridLog s Pu) (Ecompare + 4) (2Ptest) s.Pτ`) $\le N_i$; for every productive $z$: $\mathrm{path}(z).\mathrm{primes}$ = `boundedPrimes ⌈exp (2Ptest)⌉₊`, exponents `Nat.log p ⌈exp (2Ptest)⌉₊`, base and noise the two components of $z$, sample $\mathrm{sampleFn}\,z$ (noise of $z$), read-out `allocatedReplaceReadNoise B (noise) (allocatedJointFrameRead (base) (readFn z noise))`, and center $P.\mathrm{centerLift}$; $|\mathrm{Coord}_j|\le\mathrm{preparationP}$; $\|bW_j(a)\|\le\exp((\mathrm{preparationP}+2)^{c})$ with $c$ = `preparedIntegralBasisExponent m`; implicit reals $\varepsilon,\mathrm{crtBudget}$ with $0<\varepsilon\le1$, $1\le\mathrm{crtBudget}$, $\varepsilon^{-1}\le\mathrm{crtBudget}$, and $P_{\mathrm{test}},s.P_{\mathrm{bad}},s.P_{\mathrm{pres}}\in[0,\mathrm{crtBudget}]$; implicit naturals $d_0,\mathrm{old},\mathrm{removed}$ with $m\le\mathrm{degree}$, $\sum_j(\mathrm{prep}\,j).\mathrm{rank}\le m\cdot\mathrm{removed}$, $\mathrm{removed}\le\mathrm{old}$, $d\le d_0+\mathrm{degree}\cdot(\mathrm{old}-\mathrm{removed})$; and an implicit real $\mathrm{budget}$ with $1\le\mathrm{budget}$, $d_0+\mathrm{degree}\cdot\mathrm{old}\le\mathrm{budget}$, $D_{\mathrm{mod}}\le\mathrm{budget}$, $2048\,\mathrm{crtBudget}^3+(\mathrm{preparationP}+2)^{c+1}\le\mathrm{budget}$, $2\,\mathrm{normBudget}+1\le\mathrm{budget}$, $q_{\mathrm{num}}.\mathrm{capLog},q_{\mathrm{num}}.P_{\mathrm{native}},\mathrm{cost}\le\mathrm{budget}$, and $\exp(K)\le N_i$ for all $i$, where $K$ = `spatialPatchExtractionCost (recoveredKernelScalarBudget budget)` $=20\,(8(\mathrm{budget}+1)^2+1)^2$.
--
--   Conclusion: `RelativePatchSliceConclusion degree N f ((1 - ε) λ) (d₀ + degree·old) K`, i.e. there exist $q>0$, a `ResidueBoxSlice N q` $S'$, a natural number $d'$ and a `PolynomialPatch X degree d'` $A'$ with $e^{-K}N_i\le S'.\mathrm{length}_i$ for all $i$, $d'\le d_0+\mathrm{degree}\cdot\mathrm{old}$, `relativePatchComplexity A'` $\le K$, and $e^{-K}\le$ `relativePatchSliceScore S' f ((1-ε)λ) A'`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedSourceGeometryNormalizedPatchConclusion.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B304`, `OAIE3v2B266` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedSourceGeometryNormalizedPatchConclusion.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.relativePatchSliceConclusion_of_normalized_prepared_degreeRule)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B266

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X J₀ : Type} [Fintype G] [Fintype X]
variable (prep : RankPreparationFamily X J₀ m)
variable {preparationP : ℝ} {Rprep : ℕ}
variable (hprep : prep.PreparedHeights preparationP Rprep)
variable (hpPrep : 0 ≤ preparationP) (hRprep : 1 ≤ Rprep)
variable {I Eout : Fin m → Type} [∀ j, Fintype (I j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B (fun j : Fin m => (prep j).space) b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S Dmod (allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace ((fun j : Fin m => (prep j).space) j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j))
  (euclideanSubspace ((fun j : Fin m => (prep j).space) j)))]
variable (ν : ∀ j, Measure (euclideanSubspace ((fun j : Fin m => (prep j).space) j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => (prep j).Coord) j)) (euclideanSubspace ((fun j : Fin m => (prep j).space) j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers (fun j : Fin m => (prep j).space) (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) (fun j : Fin m => (prep j).space)}
variable {A : AllocatedExternalCandidateSampler B (fun j : Fin m => (prep j).space) b S hb o hR hσ N (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1)
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem
local instance instNonemptySiteCoord_r77dce8_1 : Nonempty A.Site := A.site_nonempty
variable {Y : Type} {degree d : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost childCost normBudget : ℝ} {rankBound : ℕ}
variable {productive : Finset A.Path}
variable (P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le)
  (RationalTorus.trivialFiltration degree) 0 1
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost ((A.law.mass productive /
    ((min rankBound ⌊childCost⌋₊ + 1) * (degree + 1) ^ min rankBound ⌊childCost⌋₊ : ℕ)) *
    Real.exp (-normBudget)) (Real.exp (-normBudget)))
variable {gainLog gain pGlobal : ℝ} {netExponent : ℕ}
variable (hchild : 0 ≤ childCost) (hd : d ≤ min rankBound ⌊childCost⌋₊)
  (hchildBudget : childCost ≤ normBudget)
  (hcenters : ∀ i, realPolynomialMass (patch.form.center i) ≤ normBudget)
  (hLip : (patch.kernel.lip : ℝ) ≤ Real.exp normBudget)
  (hgain : Real.exp (-gainLog) ≤ gain)
  (hReady : gain / 16 < A.law.mass productive)
  (hregularityBudget : (normBudget + 2) ^
    allocatedNormalizedShearObservableExponent degree ≤ pGlobal)
  (hpGlobal : 0 ≤ pGlobal) (hchartGlobal : chartCost ≤ pGlobal)
  (hscoreGlobal : normBudget ≤ pGlobal)
  (hmassGlobal : gainLog + 16 + ((degree : ℝ) + 1) * childCost + normBudget ≤ pGlobal)
  (hfGlobal : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
  (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
  (rule : A.DegreeGlobalizationAt (E := Eout) (fun x => ((f x - lam : ℝ) : ℂ))
    degree netExponent pGlobal cost)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : P.productive, ActualFixedSpatialForecastPath (Eout := Eout)
  B (fun j : Fin m => (prep j).space) b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B (fun j : Fin m => (prep j).space) b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : P.productive, ∀ k,
  (P.chart z).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

include ν hpPrep hRprep hchild hd hchildBudget hcenters hLip hgain hReady
  hregularityBudget hpGlobal hchartGlobal hscoreGlobal hmassGlobal hfGlobal hlam rule
  hkeep hkernel hcutoff hlate hdensity hlog hprescribed hstride in

theorem relativePatchSliceConclusion_of_normalized_prepared_degreeRule_s2
    (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
    (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget precision C Ecompare Ptest Rrank Crecovered : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : qnum.capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ qnum.E)
    (hPrecision : actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp qnum.capLog)))
    (hexcess : letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hσ1 : ∀ j, σ j ≤ 1)
    {tagCount : ℕ} (e : Fin tagCount ≃ prep.PreparedCoordinate)
    (hU : cost + cost + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      cost + cost + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) (fun j : Fin m => (prep j).space) b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).1)
        ((allocatedShortIntegerSelection (fun j : Fin m => (prep j).space) b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank ((fun j : Fin m => (prep j).space) j) ((fun j : Fin m => (prep j).poly) j))
    (sampleFn : P.productive → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : P.productive → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : P.productive, AllocatedCenteredRecoveredSampleReadAt B (fun j : Fin m => (prep j).space) bW b hb o S hR hσ
      (fun j : Fin m => (prep j).poly) (fun j => (hprep j).2.1) (allocatedShortAxis (I := I) (fun j : Fin m => (prep j).space) b S.value) spatial kernel block Crecovered
      center (path z).center (path z).base (sampleFn z) (readFn z))
    (hcost : 0 ≤ cost) (hE : 0 ≤ Ecompare) (hτ1 : τ ≤ 1)
    (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s
      (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) Ecompare ≤ S.value)
    (hξsmall : ξ ≤ Real.exp (-(2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14)))
    (hEdata : Ecompare + 8 ≤ qLate.E)
    (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
      (Dmod + Fintype.card (Σ j, I j))
      (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
      (Ecompare + 4) (2 * Ptest) s.Pτ) ≤ (N i : ℝ))
    (hprimes : ∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
    (hexponent : ∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
    (hbase : ∀ z, (path z).base = z.val.1.val)
    (hnoise : ∀ z, (path z).noise = z.val.2.val)
    (hsample : ∀ z, (path z).sample = sampleFn z z.val.2.val)
    (hread : ∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val)))
    (hcenter : ∀ z : P.productive, (path z).center = P.centerLift)
    (hcoord : ∀ j, (Fintype.card (prep j).Coord : ℝ) ≤ preparationP)
    (hbW : ∀ j a, ‖(bW j a).val‖ ≤
      Real.exp ((preparationP + 2) ^ preparedIntegralBasisExponent m))
    {ε crtBudget : ℝ} (hεpos : 0 < ε) (hεone : ε ≤ 1)
    (hCRTbudget : 1 ≤ crtBudget) (hCRTinv : ε⁻¹ ≤ crtBudget)
    (hCRTtest : Ptest ∈ Set.Icc 0 crtBudget)
    (hCRTbad : s.Pbad ∈ Set.Icc 0 crtBudget)
    (hCRTpres : s.Ppres ∈ Set.Icc 0 crtBudget)
    {d₀ old removed : ℕ}
    (hm : m ≤ degree) (hprepared : (∑ j, (prep j).rank) ≤ m * removed)
    (hremoved : removed ≤ old) (hreturned : d ≤ d₀ + degree * (old - removed))
    {budget : ℝ}
    (hFinalBudget : 1 ≤ budget)
    (hRankBudget : ((d₀ + degree * old : ℕ) : ℝ) ≤ budget)
    (hDmodBudget : (Dmod : ℝ) ≤ budget)
    (hMatrixBudget : 2048 * crtBudget ^ 3 + (preparationP + 2) ^ (preparedIntegralBasisExponent m + 1) ≤ budget)
    (hPatchCostBudget : 2 * normBudget + 1 ≤ budget)
    (hcapLog : qnum.capLog ≤ budget) (hPnative : qnum.Pnative ≤ budget)
    (hScoreBudget : cost ≤ budget)
    (hFinalLarge : ∀ i, Real.exp (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) ≤
      (N i : ℝ)) :
    RelativePatchSliceConclusion degree N f ((1 - ε) * lam) (d₀ + degree * old)
      (spatialPatchExtractionCost (recoveredKernelScalarBudget budget)) := by
  sorry

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end
