-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_exists_actual_shear_buffered_forecast_score_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_actual_shear_buffered_forecast_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:03:26.162437+00:00
-- url     : https://prove2.me/theorems/8b54ae42-9eb3-493b-8851-22fac98f73f7
-- title:
--   Some retained candidate of an allocated external-candidate conclusion carries half the output score in the actual sliced forecast target times the buffered shear score
-- statement:
--   This statement lives inside a large context of OpenAI's allocated sampling machinery; all objects below are OpenAI's and are named by their Lean names.
--
--   **Ambient data.** Fix: a natural number $m$; finite types $G$, $X$; families of finite types $I_j, J_j, E^{\mathrm{out}}_j$ ($j < m$) and naturals $n_j$; finite types $B_a$ indexed by `LayerSamplerAxis I n`; subspaces $U_j \subseteq \mathbb{R}^{J_j}$; bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; reals $R_j > 0$, $\sigma_j > 0$; a layer sampler scale `S : LayerSamplerScale B U b R σ`; naturals $D_{\mathrm{mod}}$, $L_{\mathrm{rank}}$; embeddings `spatial`, `kernel`, `block`; a finite type $T_{\mathrm{sp}}$ and an equivalence $G \simeq X \sqcup (X \sqcup T_{\mathrm{sp}})$; side lengths $N : X \to \mathbb{N}$; reals $\tau, \xi, \mathrm{cost}$; a forecast setup `s : ActualFixedSpatialForecastSetup B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (exp (-cost) / 2)`; two numerics records `qnum qLate : ActualFixedSpatialSlicedForecastNumerics s`; a proof `hb` that the $\mathbb{Z}$-span of each $b_j$ is the projected integer lattice; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb{Z}$-bases `bW j` (indexed by $E^{\mathrm{out}}_j$) of the lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)` (assumed to be a $\mathbb{Z}$-lattice); vector polynomials `poly j : VectorPolynomial X ℝ (J j → ℝ)` with all coefficients in $U_j$; left-invariant probability measures $\nu_j$ on the quotient of `euclideanSubspace (U j)` by that lattice section; compactness of `EuclideanJetLayers U (fun _ => Unit)`; strides, a finite set of column residue patterns `cells`, a point `center` of the coefficient torus, and an external candidate sampler `A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hmem τ ξ stride cells center`. Further fix a polynomial patch `patch : PolynomialPatch Y degree d` (with finitely many shear indices), a nilpotent Lie filtration `Fmark` of length $t$ on a rational Lie algebra $M$, a Lie algebra map $\varphi$ from the polynomial shear Lie algebra to $M$, a marked polynomial orbit, a function $f : \mathbb{Z}^X \to \mathbb{R}$, a real $\lambda$, reals `chartCost, massThreshold, scoreThreshold, outputMass, outputScore`, an allocated external-candidate problem `P : AllocatedExternalCandidateProblem A (polynomialShearNilmanifold …) Fmark φ marked (fun _ z => patch.shearObservable z) (fun x => f x - lam) chartCost massThreshold scoreThreshold`, a conclusion `out : P.Conclusion cost outputMass outputScore` (with its finite set of retained candidates `out.retained` and its ambient orbit `out.ambient`), reals $\delta_{\mathrm{base}}$, $P^{\mathrm{base}}_{\mathrm{pres}}$, and for each retained $z$ an actual fixed spatial forecast path `path z` (with budget `allocatedPhysicalRootBudget B U b S (fun _ => 0)`, length `S.value`, sides $N$, parameters $\tau, \delta_{\mathrm{base}}$, `s.P`, `s.Pbad`, $P^{\mathrm{base}}_{\mathrm{pres}}$). Assume:
--   - (`hkeep`) for every retained $z$ and every $k$, coordinate $k$ is kept by the chart of $z$ in `P` iff `qnum.Hchild ≤ A.sides k`;
--   - $G$ is nonempty; `qnum.Hchild ≤ S.value`; $2 \le e^{-\mathrm{cost}}\cdot$`S.value`; `qnum.δ` $\le e^{-\mathrm{cost}}$; $\mathrm{cost} + 1 \le$ `qnum.v`; $\mathrm{cost}+1 \le$ `s.Ppres`; $2e^{\mathrm{cost}} \le$ `qnum.Ptail`.
--
--   From these, for each retained $z$, OpenAI builds the dense-slice input `out.denseSliceInput s qnum z …` and the dense-slice member `member z` $=$ `(path z).toDenseSliceMember (input z)`.
--
--   **Hypotheses of the theorem.** Let $u, p, p_{\mathrm{Slice}}, p_{\mathrm{Test}}, \mathrm{localBudget}, \mathrm{precision}, C, E_{\mathrm{compare}}, P_{\mathrm{test}}, R_{\mathrm{rank}}, C_{\mathrm{recovered}}$ be reals, write $V = |$`LayerSamplerVariables G I n B`$|$, and assume:
--   - `qnum` and `qLate` have the same `δ`, `Hchild`, `v` and `Ptail`;
--   - $\xi \le 1$; for every $x \in X$, $2\cdot$`spatialTrimMargin τ N x` $\le N_x$;
--   - $u \ge 0$, $p \ge 0$, $\mathrm{localBudget} \ge 0$, $p_{\mathrm{Slice}} V \le p$, $1 \le C \le e^{p}$, `qnum.capLog` $\le p$, $2u + 4p + 12 \le$ `qnum.E`;
--   - `actualForecastDataModelRequired localBudget qnum.Pnative qnum.massLog u p` $\le \mathrm{precision}$;
--   - `A.NativeDetection 0 pSlice pTest localBudget (forecastAugmentedUnitThreshold u p (exp (pSlice * V)) C (exp qnum.capLog))`;
--   - the `excessMass` of the uniform law on `integerBox N` relative to `A.law.siteLaw (A.physicalBox …)` at level $C$ is at most $6\cdot$`positiveProjectionAccuracy precision`;
--   - $p_{\mathrm{Slice}} \ge 0$, $\mathrm{cost} \le p_{\mathrm{Slice}}$, `chartCost` $\le p_{\mathrm{Slice}}$, $p_{\mathrm{Test}} \ge 2$;
--   - $f(x) \in [0,1]$ for all $x \in$ `integerBox N`, $\lambda \in [0,1]$, $\sigma_j \le 1$ for all $j$;
--   - each `poly j` has degree at most $j + 1$ with respect to the unit weight on $X$ (`DegreeLE 1 (j+1)`);
--   - $e : \mathrm{Fin}(\mathrm{tagCount}) \simeq \Sigma_j J_j$ is an equivalence; $\mathrm{scoreLog}$, $\mathrm{massLogTransfer}$ are reals with $\mathrm{massLogTransfer} \ge 0$, $e^{-\mathrm{scoreLog}} \le$ `outputScore`, $e^{-\mathrm{massLogTransfer}} \le$ `outputMass`, $\mathrm{scoreLog} + \mathrm{massLogTransfer} + 6 \le u$;
--   - $\max(\max(\mathrm{localBudget}, 3\,\texttt{qnum.Pnative} + 3), 2u + 4p + \max(0, \texttt{qnum.massLog}) + 20) + 2 + \mathrm{massLogTransfer} + \mathrm{scoreLog} + 8 \le E_{\mathrm{compare}}$;
--   - $\max(\mathrm{localBudget}, 3\,\texttt{qnum.Pnative} + 3) \le P_{\mathrm{test}}$;
--   - for all $j$, $|\sigma_j| \le \exp(-\texttt{fixedPathSlicedPerturbationLog}\ D\ (D + \Lambda + 4)\ (\mathrm{cost}+1)\ (2\Lambda + (E_{\mathrm{compare}} + 4) + 14)\ m)$, where $D = $ `s.D` and $\Lambda = $ `s.slicedComparisonSourceLog Ptest`;
--   - `s.κ` equals `forecastGeometricJacobian U b R S.value (∏ a, basisAxisScale …) τ`, the product running over the axes selected by `allocatedShortIntegerSelection U b S.value`;
--   - $0 \le \texttt{qLate.massLog} + E_{\mathrm{compare}} + 8$;
--   - with $Q = \max(\max(\texttt{s.P}, 2\max(P_{\mathrm{test}}, 3\,\texttt{qLate.Pnative}+3) + 1), \texttt{qLate.massLog} + E_{\mathrm{compare}} + 8)$ and $a = $ `nativeForecastAmbientExponent m`: $e^{(Q + a)^a} \le N_i$ for every $i$, and $e^{(Q+a)^a} \le R_{\mathrm{rank}}$;
--   - for each $j$, `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)`;
--   - `sampleFn` and `readFn` are functions of a retained candidate and an integer array, such that for every retained $z$, `AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hmem (allocatedShortAxis U b S.value) spatial kernel block Crecovered center (path z).center (path z).base (sampleFn z) (readFn z)` holds;
--   - $\mathrm{cost} \ge 0$, $E_{\mathrm{compare}} \ge 0$, $\tau \le 1$;
--   - `ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + |Σ j, I j|) Λ (2 Ptest) Ecompare` $\le$ `S.value`;
--   - $\xi \le \exp(-(2\Lambda + (E_{\mathrm{compare}} + 4) + 14))$; $E_{\mathrm{compare}} + 8 \le$ `qLate.E`;
--   - for all $i$, $\exp(\texttt{forecastJointGridAmbientLog}\ (D_{\mathrm{mod}} + |\Sigma_j I_j|)\ (\texttt{comparisonGridLog s}\ \Lambda)\ (E_{\mathrm{compare}}+4)\ (2P_{\mathrm{test}})\ \texttt{s.Pτ}) \le N_i$;
--   - for every retained $z$: `(path z).primes` is `boundedPrimes ⌈exp (2 Ptest)⌉₊`, `(path z).exponent` is $p \mapsto \lfloor \log_p \lceil e^{2P_{\mathrm{test}}}\rceil \rfloor$ (`Nat.log`), `(path z).base` and `(path z).noise` are the two components of $z$, `(path z).sample` is `sampleFn z` at the noise of $z$, and `(path z).read` is `allocatedReplaceReadNoise B (noise of z) (allocatedJointFrameRead (base of z) (readFn z (noise of z)))`.
--
--   **Conclusion.** Let $\chi$ = `majorPhasePlateauKernel tagCount` (the patch kernel $x \mapsto$ `linearCutoff (1/8) (1/8) ‖x‖`), let `coords` = `fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)` (the map sending $x \in \mathbb{Z}^X$ to the vector whose $i$-th entry is $\mathrm{poly}_{e(i)_1}(x)_{e(i)_2}$ minus the corresponding center-lift coordinate), and let `returned` = `patch.ofTaggedWeightedShearOrbit e out.ambient`. Then there is a retained candidate $z \in$ `out.retained` such that
--   $$\frac{\texttt{outputScore}}{2} \le \mathbb{E}_{x \in \texttt{integerBox}\ N}\ \operatorname{Re}\bigl(\mathrm{target}_z(x)\bigr)\cdot \texttt{bufferedScalarScore}\ \chi\ \texttt{coords}\ T\ f\ \lambda\ x,$$
--   where $\mathrm{target}_z$ is `(member z).slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hmem s.κ`, and $T(u, \ell) = $ `returned.value` evaluated at the point whose $X$-coordinates are $u$ and whose tag coordinates are $\ell$ (both cast to reals). Here `bufferedScalarScore χ x T f λ u` $= (f(u) - \lambda)\,\chi(x(u) - [x(u)])\,T(u, [x(u)])$, with $[\cdot]$ the nearest-integer lift.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_actual_shear_buffered_forecast_score_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_actual_shear_buffered_forecast_score` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateActualShearForecastScore.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B262`, `OAIE3v2B271` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateActualShearForecastScore.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_actual_shear_buffered_forecast_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B271

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical NNReal Matrix TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I J Eout : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  [∀ j, Fintype (Eout j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {N : X → ℕ} {τ ξ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable (qnum qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
variable {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
variable {hmem : ∀ j d, coefficients (poly j) d ∈ U j}
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable {stride : X → ℕ}
variable {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hmem
  τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem.Conclusion
attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_5
variable {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {degree d t : ℕ}
variable (patch : PolynomialPatch Y degree d) [Fintype (PolynomialShearIndex patch.weight)]
variable {Fmark : NilpotentLieFiltration M t}
variable {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
variable {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
variable (f : (X → ℤ) → ℝ) (lam : ℝ)
variable {chartCost massThreshold scoreThreshold outputMass outputScore : ℝ}
variable {P : AllocatedExternalCandidateProblem (E := Eout) A
  (polynomialShearNilmanifold patch.weight degree patch.weight_le) Fmark φ marked
  (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
  chartCost massThreshold scoreThreshold}
variable (out : P.Conclusion cost outputMass outputScore)
variable {δbase PpresBase : ℝ}
variable (path : ∀ _z : out.retained, ActualFixedSpatialForecastPath (Eout := Eout)
  B U b S hR hσ Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) N τ δbase s.P s.Pbad PpresBase)
variable (hkeep : ∀ z : out.retained, ∀ k,
  (P.chart ⟨z.val, out.subset z.property⟩).keep k ↔ qnum.Hchild ≤ A.sides k)
variable (hkernel : Nonempty G) (hcutoff : qnum.Hchild ≤ S.value)
variable (hlate : 2 ≤ Real.exp (-cost) * (S.value : ℝ))
variable (hdensity : qnum.δ ≤ Real.exp (-cost)) (hlog : cost + 1 ≤ qnum.v)
variable (hprescribed : cost + 1 ≤ s.Ppres) (hstride : 2 * Real.exp cost ≤ qnum.Ptail)

local notation "input" z => out.denseSliceInput s qnum z (hkeep z) (ActualFixedSpatialForecastPath.commonTuple (path z))
  hkernel hcutoff hlate hdensity le_rfl hlog hprescribed hstride
local notation "member" z => ActualFixedSpatialForecastPath.toDenseSliceMember (path z) (input z)

include ν in

theorem exists_actual_shear_buffered_forecast_score_s2
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
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcostSlice : cost ≤ pSlice) (hchartCost : chartCost ≤ pSlice)
    (htest : 2 ≤ pTest)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    {scoreLog massLogTransfer : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * qnum.Pnative + 3))
        (2 * u + 4 * p + max 0 qnum.massLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcommonTest : max localBudget (3 * qnum.Pnative + 3) ≤ Ptest)
    (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
      s.D (s.D + s.slicedComparisonSourceLog Ptest + 4) (cost + 1)
      (2 * s.slicedComparisonSourceLog Ptest + (Ecompare + 4) + 14) m))
    (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1)
        ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
    (hEprec : 0 ≤ qLate.massLog + Ecompare + 8)
    (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ (N i : ℝ))
    (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1))
      (qLate.massLog + Ecompare + 8) + nativeForecastAmbientExponent m) ^
      nativeForecastAmbientExponent m) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (sampleFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : out.retained → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I Eout n B → ℤ)
    (hglobal : ∀ z : out.retained, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
      poly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block Crecovered
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
      (allocatedJointFrameRead z.val.1.val (readFn z z.val.2.val))) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N,
        ((member z).slice.target (allocatedShortIntegerSelection U b S.value) s.hBactive
          o bW hb poly hmem s.κ x).re *
        bufferedScalarScore χ coords
          (fun u lifts => returned.value
            (Sum.elim (fun i => (u i : ℝ)) (fun i => (lifts i : ℝ)))) f lam x.val := by
  sorry

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end
