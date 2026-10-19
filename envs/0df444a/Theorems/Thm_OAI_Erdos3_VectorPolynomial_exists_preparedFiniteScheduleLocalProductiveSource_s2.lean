-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteScheduleLocalProductiveSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T08:22:17.747421+00:00
-- url     : https://prove2.me/theorems/bcc66684-4be0-4dc2-ab34-4e3631f4d204
-- title:
--   For a rank-preparation family there is a common sampler scale meeting all prepared finite-schedule geometry, scalar, availability and productive-source requirements
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Data.** Let $m, n_X, M$ be natural numbers, $X_0, J_0$ types, and `prep : RankPreparationFamily X₀ J₀ m` (a rank preparation layer for each $j < m$, with a finite coordinate type $\mathrm{Coord}_j$ = `(prep j).Coord`, assumed to have decidable equality). Let $U_j \subseteq \mathbb{R}^{\mathrm{Coord}_j}$ be subspaces, `b j` bases (indexed by $\mathrm{Fin}$ of `preparedSamplerTransverse prep j`) of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is the projected integer lattice (`hb`), `stride, N : Fin nX → ℕ`, a polynomial $P_{\mathrm{detect}} \in \mathbb{N}[X]$, $V_{\mathrm{tail}} : \mathrm{Fin}(m) \to \mathbb{R}_{\ge 0}$, finite types $Q_j$, orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by `PreparedSamplerContinuous prep j`, and `bW j` $\mathbb{Z}$-bases (indexed by $Q_j$) of the lattice section $\Lambda_j$ of $\mathbb{Z}^{\mathrm{Coord}_j}$ in `euclideanSubspace (U j)`, each $\Lambda_j$ a $\mathbb{Z}$-lattice. Let $\nu_j$ be left-invariant probability measures on `euclideanSubspace (U j)` $/\Lambda_j$. Put $b_0$ = `modularInitialBlockCount m (nX + m * M)`, $G^\ast$ = `EnlargedPreparedCommonKernel m b₀`, $\mathcal{B}$ = `EnlargedPreparedCommonSamplerBlock prep b₀`, $\mathrm{Var}$ = `LayerSamplerVariables G* (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) 𝓑`, and $V = |\mathrm{Var}|$. Let $\mu$ be a left-invariant probability measure on the (compact, Borel) coefficient torus `CoefficientTorus (K := Var) U`, and $\mu_{\mathrm{rows}}$ a left-invariant probability measure on the (compact, Borel) coefficient torus `CoefficientTorus (K := Fin 1) U`; the site torus `SiteTorus (Finset (Fin 1)) U` carries a Borel measurable structure. Let $K$ be a finite type, `degree, Cdetect : K → ℕ`, and $k_{\mathrm{model}} \in K$. Let $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, u, p, \mathrm{forecastCap}$ be reals, `sourceU, modelLog, sliceLog : K → ℝ`, reals $Q_\sigma, Q_w, P_{\min}, \mathrm{requestedCoarse}, \mathrm{gainLog}, \mathrm{gain}, V_{\log}$, and natural numbers $L_{\min}, Q_{\mathrm{good}}$.
--
--   **Hypotheses.** $\mathrm{degree}(k) \le m$ for all $k$; $\mathrm{degree}(k_{\mathrm{model}}) = 0$; $\mathrm{Cdetect}(k_{\mathrm{model}})$ = `sampledSupportedSlicedDetectionConstant 0 Pdetect`; $\mathrm{sourceU}(k_{\mathrm{model}}) = u + 2p + 1$; $m > 0$; $n_X > 0$; $|\mathrm{Coord}_j| \le M$ for all $j$; $B_{\mathrm{struct}} \ge 0$, $u \ge 0$, $p \ge 0$; $\mathrm{sourceU}(k) \ge 0$, $\mathrm{modelLog}(k) \ge 0$, $\mathrm{sliceLog}(k) \le \mathrm{modelLog}(k)$ and $V \le e^{\mathrm{modelLog}(k)}$ for all $k$; $Q_{\mathrm{stride}}, Q_\sigma, Q_w, P_{\min} \ge 0$; $L_{\min} \le e^{P_{\min}}$; $\mathrm{gainLog} \ge 0$, $V_{\log} \ge 0$; $1 \le Q_{\mathrm{good}} \le e^{V_{\log}}$; $e^{-\mathrm{gainLog}} \le \mathrm{gain}$; $n_X \le B_{\mathrm{struct}}$; $\mathrm{gainLog} \le B_{\mathrm{struct}}$.
--
--   **Abbreviations** (each a real number or real function of $s \in K$, built from OpenAI's explicit budget functions):
--   - $p_{\mathrm{num}}$ = `enlargedPreparedCommonSamplerDimension m M b₀`; $R_j$ = `allocatedCommonProductRadius m Bstruct Bstruct` (the same for all $j$); $p_{\mathrm{Radius}}$ = `allocatedCommonProductRadiusLog m Bstruct Bstruct`; $D$ = `allocatedComparisonDimension m pnum`;
--   - $p_{\mathrm{Detect}}(s)$ = `allocatedModelTestLog (sourceU s) (modelLog s)`; $a_{\mathrm{Detect}}(s) = 2\,\mathrm{sourceU}(s) + 4\,\mathrm{modelLog}(s) + 7$;
--   - $\mathrm{detectionGain}(s)$ = `slicedDetectionGainLog (degree s) (Cdetect s) V (pDetect s) (pDetect s) (aDetect s)`;
--   - $P_k(s)$ = `scalarKernelLogarithmicBudget (Fin (degree s + 1)) G* (detectionGain s + pDetect s + 4)`;
--   - $P_{\mathrm{physical}}(s)$ = `preparedFiniteScheduleLocalPhysical m nX V Qstride (Pk s)`;
--   - $\mathrm{target}(s) = \mathrm{detectionGain}(s) + 40 + \texttt{coefficientErrorSpatialLog}(P_{\mathrm{physical}}(s))$;
--   - $E(s) = \mathrm{target}(s) + D\cdot(m2^{m+1}P_k(s)) + 5$;
--   - $P_\rho(s) = 2\cdot\texttt{affineProfileInputEnvelope}\ D\ \texttt{canonicalSublevelCutoffLip}\ \texttt{canonicalTransitionLip}\ (E(s))\ (p_{\mathrm{Detect}}(s) + 2) + 2$;
--   - $P_{\mathrm{tail}}(s)$ = `affineProfileToleranceEnvelope m D (D(D+1) + D·D + D + 1) canonicalSublevelCutoffLip canonicalTransitionLip (E s) (pDetect s + 2)`;
--   - $P_{\mathrm{scale}}$ = `preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ`;
--   - $T_{\mathrm{mod}}(s) = (m+1)P_k(s) + n_X Q_{\mathrm{stride}}$;
--   - $\mathrm{lengthLogs}(s)$ = `allocatedAffineLengthLog m D Pscale (Prho s) (Pk s) (target s) (pDetect s + 2) (Tmod s)`;
--   - $P_{\mathrm{seed}}$ = `allocatedScaleLog (Pscale + Σ_s lengthLogs s + Pmin + 1)`;
--   - $W$ = `physicalBadProductGap (b₀ * (nX + m * M)) (gainLog + 8) Vlog Qgood`;
--   - $P_{\mathrm{master}}(s)$ = `preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride (Pphysical s) (sourceU s) (modelLog s) (Prho s) (target s) (detectionGain s)`;
--   - `coarseTarget` = `preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse`;
--   - $P_{\mathrm{late}} = \sum_{s \in K}$ `preparedUniformDegreeDirectLate (Pmaster s) Pscale (Pphysical s) coarseTarget (allocatedWitnessScaleLog Pseed Qw)`;
--   - $\tau = \exp(-(\mathrm{gainLog} + n_X + 8))$.
--
--   **Statement.** Assume further $p_{\mathrm{num}} \le B_{\mathrm{struct}}$, $W \le e^{Q_w}$, $\mathrm{sliceLog}(k_{\mathrm{model}})\cdot V \le p$, $4\prod_j \texttt{earlyConstantDensityCap}\ |\texttt{PreparedSamplerContinuous prep j}|\ (\texttt{preparedSamplerTransverse prep j})\ R_j\ V_{\mathrm{tail}}(j) \le e^{p}$, and $0 \le \mathrm{forecastCap} \le e^{p}$. Then $R_j > 0$ for all $j$, and there are a real $\sigma > 0$ and a layer sampler scale `S : LayerSamplerScale 𝓑 U b R (fun _ => σ)` (over $G^\ast$, `PreparedSamplerContinuous prep`, `preparedSamplerTransverse prep`, $\mathrm{Coord}$) such that:
--   1. $0 \le p_{\mathrm{Radius}}$, and $R_j \le 1$ and $R_j^{-1} \le e^{p_{\mathrm{Radius}}}$ for all $j$;
--   2. $\sigma \le 1$, $\sigma \le e^{-Q_\sigma}$, $\sigma^{-1} \le e^{P_{\mathrm{scale}}}$;
--   3. $L_{\min} \le \texttt{S.value} \le \exp(\texttt{allocatedWitnessScaleLog}\ P_{\mathrm{seed}}\ Q_w)$;
--   4. for all $j$ and $i$ with $\texttt{S.value}^{j+1} <$ `basisAxisScale (b j) i`: $8\cdot\texttt{probabilityProfileLipschitz}\cdot W \le \bigl(\texttt{layerSamplerGapWidth}\ \mathcal{B}\ R\ (j,i)/2\bigr)\cdot\bigl(\texttt{basisAxisScale (b j) i}/\texttt{S.value}^{j+1}\bigr)$;
--   5. for every $s \in K$, `PreparedUniformDegreeGeometryAt 𝓑 U b S (degree s) (Cdetect s) nX Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)`;
--   6. for every $k \in K$, `PreparedUniformDegreeDirectScalarBounds m (degree k) nX V (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)`;
--   7. for every $k$ with $\mathrm{Cdetect}(k)$ = `sampledSupportedSlicedDetectionConstant (degree k) Pdetect`, `PreparedScheduledDirectSourceAvailability` holds (for $\mathcal{B}$, $U$, $b$, $S$, the positivity proofs of $R$ and $\sigma$, the selection `enlargedPreparedCommonCanonicalSelection m b₀ (degree k) _`, stride, $N$, $P_{\mathrm{detect}}$, sourceU $k$, modelLog $k$, sliceLog $k$, $V_{\mathrm{tail}}$, $\tau$, `hb`, $o$, with parameters $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}(k), P_{\mathrm{late}}, \mathrm{detectionGain}(k), P_{\mathrm{physical}}(k)$, `coarseTarget`);
--   8. for every $k$ with $\mathrm{degree}(k) = 0$ and $\mathrm{Cdetect}(k)$ = `sampledSupportedSlicedDetectionConstant 0 Pdetect`, `PreparedScheduledModelAvailability` holds with the same arguments (selection taken at degree $0$) and the measure $\mu$;
--   9. for every $k$ with $\mathrm{Cdetect}(k)$ = `sampledSupportedSlicedDetectionConstant (degree k) Pdetect`, `PreparedScheduledDegreeModelAvailability` holds with the same arguments as in 7 and the measure $\mu$;
--   10. `PreparedUniformDegreeProductiveSourceConclusion` holds for $m, n_X, M$, `prep`, $U$, $b$, $S$, the positivity proofs, stride, $N$, $P_{\mathrm{detect}}$, pModel $=\mathrm{modelLog}(k_{\mathrm{model}})$, pSlice $=\mathrm{sliceLog}(k_{\mathrm{model}})$, $V_{\mathrm{tail}}$, $\tau$, $u$, $p$, forecastCap, `hb`, $o$, `bW`, $\mu$, and parameters $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}(k_{\mathrm{model}}), P_{\mathrm{late}}, \mathrm{detectionGain}(k_{\mathrm{model}}), P_{\mathrm{physical}}(k_{\mathrm{model}})$, `coarseTarget`, $p_{\mathrm{Radius}}, P_{\mathrm{scale}}, P_{\mathrm{seed}}, Q_w, \mathrm{gainLog}, \mathrm{gain}, V_{\log}, Q_{\mathrm{good}}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleLocalProductiveSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B285`, `OAIE3v2B290` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteScheduleLocalProductiveSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B290

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteScheduleLocalProductiveSource_s2
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0)

    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    {K : Type} [Fintype K] (degree Cdetect : K → ℕ) (kModel : K)
    (hdegree : ∀ k, degree k ≤ m) (hdegreeZero : degree kModel = 0)
    (hCzero : Cdetect kModel = sampledSupportedSlicedDetectionConstant 0 Pdetect)
    (Bstruct Qstride u p forecastCap : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hModelSource : sourceU kModel = u + 2 * p + 1)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount m (nX + m * M)) * (nX + m * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    sliceLog kModel * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, degree k = 0 →
        Cdetect k = sampledSupportedSlicedDetectionConstant 0 Pdetect →
        PreparedScheduledModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := m) (nX := nX) (M := M) (prep := prep) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
