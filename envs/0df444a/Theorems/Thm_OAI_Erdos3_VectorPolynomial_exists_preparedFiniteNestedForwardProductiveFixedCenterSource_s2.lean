-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T08:23:54.689314+00:00
-- url     : https://prove2.me/theorems/39b9ce17-c39d-4c11-9387-3146a291d6ce
-- title:
--   Existence of a layer sampler scale with uniform-degree geometry, direct source and model availability, a productive source conclusion, and a good-center ready conclusion
-- statement:
--   All objects named in backticks are defined by OpenAI; hypothesis names in parentheses are those of the Lean statement. This is a scheduling statement whose budgets are long chains of OpenAI's explicit real-valued functions; they are listed by name.
--
--   **Setting.** Let $n_X, m, M$ be natural numbers, $X_0, J_0$ types, and `prep` a `RankPreparationFamily X₀ J₀ m` (a family of $m$ rank preparation layers, each with finite coordinate, column and row types, labels, rational matrices and a vector polynomial). Let $\mathrm{outerDepth}, \mathrm{innerDepth}, \mathrm{cutoff}$ be natural numbers and put $m' = \max(m, \mathrm{cutoff})$; let $\mathrm{prep}'$ = `prep.pad m'` (the family extended by empty layers to length $m'$), $J'_j$ = the coordinate type of $\mathrm{prep}'_j$ (assumed to have decidable equality), $I'$ = `PreparedSamplerContinuous prep'`, $n'$ = `preparedSamplerTransverse prep'`, $k_0$ = `modularInitialBlockCount m' (nX + m' M)`, $G'$ = `EnlargedPreparedCommonKernel m' k₀`, $B'$ = `EnlargedPreparedCommonSamplerBlock prep' k₀`, and $\mathrm{Vars}$ = `LayerSamplerVariables G' I' n' B'`. Let $U_j$ be a real subspace of $J'_j \to \mathbb{R}$ and $b_j$ a real basis indexed by $\operatorname{Fin} n'_j$ of the orthogonal complement of `euclideanSubspace (U j)`, for $j \in \operatorname{Fin} m'$. Let $\mathrm{stride}, N : \operatorname{Fin} n_X \to \mathbb{N}$ and $V_{\mathrm{tail}} : \operatorname{Fin} m' \to \mathbb{R}_{\ge 0}$. Let $Q_j$ be finite types; assume the integer span of $b_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))` (hb); let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I'_j$ and $bW_j$ a $\mathbb{Z}$-basis indexed by $Q_j$ of the lattice section $\mathbb{Z}^{J'_j} \cap$ `euclideanSubspace (U j)`, assumed to be a $\mathbb{Z}$-lattice. Let $\nu_j$ be left-invariant probability measures on the quotient tori. Assume `CoefficientTorus U` for variables $\mathrm{Vars}$ is compact with a Borel measurable structure and let $\mu$ be a left-invariant probability measure on it; assume likewise for `CoefficientTorus U` with variables $\operatorname{Fin}(0+1)$, with a left-invariant probability measure $\mu_{\mathrm{rows}}$, and that `SiteTorus (Finset (Fin (0+1))) U` carries a Borel measurable structure (these last data, and $\nu$, are binders of the statement that are not used anywhere else in it).
--
--   **Hypotheses.** Let $A, C_{\mathrm{slice}}, C_{\mathrm{direct}}$ be natural numbers and $\mathrm{stageCountConstant} : \mathbb{N} \to \mathbb{N}$ with $A \ge 2$ and $C_{\mathrm{slice}} + 1 \le A$. Let $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, \mathrm{forecastCap}, \mathrm{stageLog}, E_{\mathrm{conditional}}, Q_\sigma, Q_w, P_{\min}, \mathrm{requestedCoarse}, \mathrm{gainLog}, \mathrm{gain}, V_{\log}$ be reals and $L_{\min}, Q_{\mathrm{good}}$ natural numbers. Assume:
--   - $m' > 0$, $n_X > 0$, every coordinate type of `prep` has at most $M$ elements (hCoord);
--   - $B_{\mathrm{struct}} \ge 0$, $\mathrm{stageLog} \in [0, B_{\mathrm{struct}}]$, $Q_{\mathrm{stride}} \ge 0$, $Q_\sigma \ge 0$, $Q_w \ge 0$, $P_{\min} \ge 0$, $L_{\min} \le e^{P_{\min}}$, $\mathrm{gainLog} \ge 0$, $V_{\log} \ge 0$, $Q_{\mathrm{good}} \ge 1$, $Q_{\mathrm{good}} \le e^{V_{\log}}$, $e^{-\mathrm{gainLog}} \le \mathrm{gain}$, $n_X \le B_{\mathrm{struct}}$, $\mathrm{gainLog} \le B_{\mathrm{struct}}$;
--   - $\mathrm{stride}(i) > 0$ and $\mathrm{stride}(i) \le e^{Q_{\mathrm{stride}}}$ for all $i$;
--   - $C : \operatorname{Fin} m' \to \mathbb{R}$ with $0 \le C_j \le e^{B_{\mathrm{struct}}}$ and $\|\chi_j^{-1} v\| \le C_j \|v\|$ for all $v$, where $\chi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`; $C^{\mathrm{fwd}} : \operatorname{Fin} m' \to \mathbb{R}_{\ge 0}$ with $\|\chi_j v\| \le C^{\mathrm{fwd}}_j \|v\|$ and $C^{\mathrm{fwd}}_j \le e^{B_{\mathrm{struct}}}$;
--   - $V_{\mathrm{tail}}(j) \le e^{B_{\mathrm{struct}}}$ and $0 \le$ `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le V_{\mathrm{tail}}(j)$ for all $j$ (this ratio is the covolume of the lattice section divided by $\prod_i$ `basisAxisScale (b j) i`);
--   - `probabilityProfileLipschitz` $\le e^{B_{\mathrm{struct}}}$ and `normalizedSiteCutoffBound` $\le e^{B_{\mathrm{struct}}}$ (two constants fixed by OpenAI);
--   - `cells` is a nonempty finite set of column residue patterns on $\operatorname{Option}(\mathrm{Vars}) \times \operatorname{Fin} n_X$ modulo $\mathrm{stride}$;
--   - $\mathrm{poly}_j \in$ `VectorPolynomial (Fin nX) ℝ (J'_j → ℝ)` of total degree at most $j+1$ (hp) with all coefficients in $U_j$ (hmem);
--   - $R_{\mathrm{rank}}$ is real and `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)` for all $j$ (hrank);
--   - $\mathrm{test} : \mathbb{R}^{n_X} \to \mathbb{R}$ with $|\mathrm{test}(x)| \le 1$ for all $x$, and $\mathrm{gain} \le$ the average of $\mathrm{test}(x)$ over $x \in$ `integerBox N` (hmean).
--
--   **Derived quantities.** Let $P_{\mathrm{detect}}$ = `preparedFiniteForwardDetectorPolynomial cutoff`; $K$ = `PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff` with degree map `preparedFiniteNestedForwardAllDegreeDegree` and anchor $k_{\mathrm{Model}}$ = `preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff`; $C_{\mathrm{detect}}(k)$ = `sampledSupportedSlicedDetectionConstant (degree k) Pdetect`. For $k \in K$, with stage $\mathrm{st}(k)$ = `preparedFiniteNestedForwardAllDegreeStage k` and seed $\mathrm{sd}(k)$ = `preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k`: $\mathrm{sourceU}(k)$ = `preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant st(k) (preparedFiniteNestedForwardAllDegreeIsDirect k) sd(k) gainLog stageLog`; $\mathrm{modelLog}(k)$ = `preparedFiniteForwardWork A stageCountConstant st(k) sd(k)`; $\mathrm{sliceLog}(k) = (\texttt{preparedFiniteForwardParameter A stageCountConstant st(k) sd(k)} + C_{\mathrm{slice}})^{C_{\mathrm{slice}}}$. With $\mathrm{seed}^*$ = `candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct`: $u$ = `preparedFiniteForwardModelPrecision A stageCountConstant innerDepth seed* gainLog stageLog` and $p$ = `preparedFiniteForwardWork A stageCountConstant innerDepth seed*`. Further $p_{\mathrm{num}}$ = `enlargedPreparedCommonSamplerDimension m' M k₀`; $R_j$ = `allocatedCommonProductRadius m' Bstruct Bstruct` (constant in $j$); $p_{\mathrm{Radius}}$ = `allocatedCommonProductRadiusLog m' Bstruct Bstruct`; $D$ = `allocatedComparisonDimension m' pnum`; $p_{\mathrm{Detect}}(k)$ = `allocatedModelTestLog (sourceU k) (modelLog k)`; $a_{\mathrm{Detect}}(k) = 2\,\mathrm{sourceU}(k) + 4\,\mathrm{modelLog}(k) + 7$; $\mathrm{detectionGain}(k)$ = `slicedDetectionGainLog (degree k) (Cdetect k) (#Vars) (pDetect k) (pDetect k) (aDetect k)`; $P_k(k)$ = `scalarKernelLogarithmicBudget (Fin (degree k + 1)) G' (detectionGain k + pDetect k + 4)`; $P_{\mathrm{physical}}(k)$ = `preparedFiniteScheduleLocalPhysical m' nX (#Vars) Qstride (Pk k)`; $\mathrm{target}(k) = \mathrm{detectionGain}(k) + 40 +$ `coefficientErrorSpatialLog (Pphysical k)`; $E(k) = \mathrm{target}(k) + D \cdot (m' 2^{m'+1}) P_k(k) + 5$; $P_\rho(k) = 2 \cdot$ `affineProfileInputEnvelope D canonicalSublevelCutoffLip canonicalTransitionLip (E k) (pDetect k + 2)` $+ 2$; $P_{\mathrm{tail}}(k)$ = `affineProfileToleranceEnvelope m' D (D(D+1) + D·D + D + 1) canonicalSublevelCutoffLip canonicalTransitionLip (E k) (pDetect k + 2)`; $P_{\mathrm{scale}}$ = `preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ`; $T_{\mathrm{mod}}(k) = (m'+1) P_k(k) + n_X Q_{\mathrm{stride}}$; $\mathrm{lengthLogs}(k)$ = `allocatedAffineLengthLog m' D Pscale (Prho k) (Pk k) (target k) (pDetect k + 2) (Tmod k)`; $P_{\mathrm{seed}}$ = `allocatedScaleLog (Pscale + Σ_k lengthLogs k + Pmin + 1)`; $W$ = `physicalBadProductGap (k₀ * (nX + m' M)) (gainLog + 8) Vlog Qgood` (its first argument is the product $k_0 (n_X + m' M)$); $P_{\mathrm{master}}(k)$ = `preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)`; $\mathrm{coarseTarget}$ = `preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse`; $P_{\mathrm{late}} = \sum_{k} $ `preparedUniformDegreeDirectLate (Pmaster k) Pscale (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)`; $\tau = \exp(-(\mathrm{gainLog} + n_X + 8))$; $\alpha(k) = \exp(-(2 \cdot \texttt{preparedFiniteForwardModelPrecision A stageCountConstant st(k) sd(k) gainLog stageLog} + 4\,\mathrm{modelLog}(k) + 8))$; $B_0$ = `preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog`; $P_{\mathrm{width}} = 4 (P_{\mathrm{late}} + 8)^2$; $B_{\mathrm{cert}}$ = `preparedForecastGoodCertificateBudget B₀ Bstruct Pwidth gainLog Vlog`; $P_{\mathrm{good}}$ = `preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent m') B₀ Bstruct Pwidth gainLog Vlog`; $\mathrm{anchorRequired}$ = `preparedFiniteScheduleAnchorGoodRequired m' (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth`; $\mathrm{conditionalRequired}$ = `preparedConditionalExcessRequired m' Plate Econditional`; $\mathrm{detectorRequired}(k)$ = the `required` field of `preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m' (degree k)) (degree k + 1) (Pmaster k) Plate`; and $R_{\mathrm{req}}$ = `preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct anchorRequired conditionalRequired detectorRequired`. Write $\mathrm{Cap} = 4 \prod_j$ `earlyConstantDensityCap (#I'_j) (n'_j) (R j) (Vtail j)`.
--
--   **Conclusion.** Assume further $p_{\mathrm{num}} \le B_{\mathrm{struct}}$, $W \le e^{Q_w}$, $\mathrm{Cap} \le e^p$, $0 \le \mathrm{forecastCap} \le e^p$, $e^{R_{\mathrm{req}}} \le N(i)$ for all $i$, and $e^{R_{\mathrm{req}}} \le R_{\mathrm{rank}}$. Then $R_j > 0$ for all $j$, and there exist a real $\sigma > 0$ and a `LayerSamplerScale B' U b R (fun _ => σ)` $S$ (for kernel $G'$, continuous index types $I'$, transverse counts $n'$, coordinate types $J'$) such that:
--   - $0 \le p_{\mathrm{Radius}}$; $R_j \le 1$ and $R_j^{-1} \le e^{p_{\mathrm{Radius}}}$ for all $j$; $\sigma \le 1$, $\sigma \le e^{-Q_\sigma}$, $\sigma^{-1} \le e^{P_{\mathrm{scale}}}$; $L_{\min} \le \texttt{S.value} \le \exp(\texttt{allocatedWitnessScaleLog Pseed Qw})$;
--   - for all $j, i$ with $\texttt{S.value}^{j+1} <$ `basisAxisScale (b j) i`: $8 \cdot \texttt{probabilityProfileLipschitz} \cdot W \le (\texttt{layerSamplerGapWidth B' R ⟨j, i⟩}/2) \cdot \texttt{basisAxisScale (b j) i} / \texttt{S.value}^{j+1}$;
--   - for every $s \in K$: `PreparedUniformDegreeGeometryAt B' U b S (degree s) (Cdetect s) nX Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)`;
--   - for every $k \in K$: `PreparedUniformDegreeDirectScalarBounds m' (degree k) nX (#Vars) (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)`;
--   - for every $k$: `PreparedScheduledDirectSourceAvailability` and `PreparedScheduledDegreeModelAvailability` hold (the latter with the measure $\mu$), both for $B', U, b, S$, the positivity facts of $R$ and $\sigma$, the canonical selection `enlargedPreparedCommonCanonicalSelection m' k₀ (degree k) _`, $\mathrm{stride}, N, P_{\mathrm{detect}}$, $\mathrm{sourceU}(k), \mathrm{modelLog}(k), \mathrm{sliceLog}(k)$, $V_{\mathrm{tail}}, \tau, \mathrm{hb}, o$, and $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}(k), P_{\mathrm{late}}, \mathrm{detectionGain}(k), P_{\mathrm{physical}}(k), \mathrm{coarseTarget}$;
--   - `PreparedUniformDegreeProductiveSourceConclusion` holds for $m', n_X, M, \mathrm{prep}', U, b, S$, the positivity facts, $\mathrm{stride}, N, P_{\mathrm{detect}}$, $\mathrm{modelLog}(k_{\mathrm{Model}}), \mathrm{sliceLog}(k_{\mathrm{Model}})$, $V_{\mathrm{tail}}, \tau, u, p, \mathrm{forecastCap}, \mathrm{hb}, o, bW, \mu$ and $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}(k_{\mathrm{Model}}), P_{\mathrm{late}}, \mathrm{detectionGain}(k_{\mathrm{Model}}), P_{\mathrm{physical}}(k_{\mathrm{Model}}), \mathrm{coarseTarget}, p_{\mathrm{Radius}}, P_{\mathrm{scale}}, P_{\mathrm{seed}}, Q_w, \mathrm{gainLog}, \mathrm{gain}, V_{\log}, Q_{\mathrm{good}}$;
--   - and $2 \cdot$ `spatialTrimMargin τ N i` $\le N(i)$ for all $i$, $e^{-P_{\mathrm{late}}} \le 1$, and there is a proof `Acandidate` of `AllocatedExternalCandidateSamplerFamily B' U b S hb o hR (fun _ => hσ) N poly hmem τ (exp(-Plate)) stride cells` (that is, `AllocatedExternalCandidateSampler` holds at every center of the coefficient torus) such that `PreparedCenteredProductiveGoodCenterReadyConclusion prep' U b S bW hb o hR (fun _ => hσ) μ poly hmem stride` holds with widths `allocatedExternalCandidateWidths B' U b S N τ (exp(-Plate))`, bases `(Acandidate 0).bases`, $\mathrm{gainLog}, \mathrm{gain}, Q_{\mathrm{good}}$, the embedding `preparedSpatialKernelBlocks m' M nX`, the law `Acandidate.law`, $N$, `test`, and the readiness predicate on centers $c$: for every $k \in K$, `(Acandidate c).NativeDetection (degree k) (sliceLog k) (P_detect evaluated at pDetect k) β_k (α k)` holds, where $\beta_k$ is the `nativeBudget` field of the detector resources above, and the excess mass (`excessMass`: $\sum_x \max(q(x) - \mathrm{Cap}\cdot p(x), 0)$) of the site law `(Acandidate c).law.siteLaw ((Acandidate c).physicalBox _ _)` over the uniform weights $p$ on `integerBox N`, at level $\mathrm{Cap}$, is at most $6 \cdot$ `positiveProjectionAccuracy Econditional` $= 6 e^{-(2 E_{\mathrm{conditional}} + 4)}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteNestedForwardCanonicalFixedCenterSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B285`, `OAIE3v2B290` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteNestedForwardCanonicalFixedCenterSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardProductiveFixedCenterSource)

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
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardProductiveFixedCenterSource_s2
    {m M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m) (outerDepth innerDepth cutoff : ℕ)
    [∀ j : Fin (max m cutoff), DecidableEq (RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse (prep.pad (max m cutoff))) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ)
    (Vtail : Fin (max m cutoff) → ℝ≥0)

    (Q : Fin (max m cutoff) → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    (A Cslice Cdirect : ℕ) (stageCountConstant : ℕ → ℕ)
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A)
    (Bstruct Qstride forecastCap stageLog Econditional : ℝ)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin (max m cutoff) → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Bstruct)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin (max m cutoff) → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Bstruct)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Bstruct)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (Fin nX) stride))
    (hCells : cells.Nonempty)
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (Rrank : ℝ)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    (∀ i, Real.exp Rreq ≤ (N i : ℝ)) → Real.exp Rreq ≤ Rrank →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N poly hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N test
        (fun center =>
          letI : DecidableEq (Fin nX) := Classical.decEq _
          (∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
