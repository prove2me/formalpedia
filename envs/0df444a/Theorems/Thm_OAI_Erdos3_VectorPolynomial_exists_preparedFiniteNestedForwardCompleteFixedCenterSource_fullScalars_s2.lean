-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T09:13:20.258668+00:00
-- url     : https://prove2.me/theorems/b2085a7c-2d05-4714-a809-6fed0704a6b6
-- title:
--   Existence of a sampler scale with all scalar budgets and fixed-center source conclusions for the prepared finite nested forward schedule
-- statement:
--   This statement is long; we describe its parts in the order of the Lean statement. Throughout, $m' = \max(m, \mathrm{cutoff})$ and $J_{\mathrm{alloc}}$ = `modularInitialBlockCount m' (nX + m' * M)` (an explicit natural number of OpenAI).
--
--   **Data.** Let $n_X, m, M$ be natural numbers, $X_0, J_0$ types, and `prep` a `RankPreparationFamily X₀ J₀ m` (OpenAI's family of $m$ rank-preparation layers, each with a finite coordinate type `Coord`); let `prep.pad m'` be its padding by empty layers to $m'$ layers, and write $\mathrm{Coord}_j$ for the coordinate type of layer $j$ of `prep.pad m'` (assumed to have decidable equality). Let `outerDepth`, `innerDepth`, `cutoff` be natural numbers. For $j \in \operatorname{Fin} m'$ let $U_j$ be a real subspace of $\mathrm{Coord}_j \to \mathbb{R}$; let $b_j$ be a real basis of the orthogonal complement of `euclideanSubspace (U j)` (that subspace in Euclidean space; defined by OpenAI), indexed by $\operatorname{Fin}$ of `preparedSamplerTransverse (prep.pad m') j` (OpenAI's transverse dimension), whose integer span equals `projectedIntegerLattice` (hb); let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by `PreparedSamplerContinuous (prep.pad m') j`; let $Q_j$ be finite types and $bW_j$ a $\mathbb{Z}$-basis, indexed by $Q_j$, of `latticeSection` (the lattice $\mathbb{Z}^{\mathrm{Coord}_j} \cap$ `euclideanSubspace (U j)`), assumed to be a full lattice. Let $\mathrm{stride}, N : \operatorname{Fin} n_X \to \mathbb{N}$ and $V_{\mathrm{tail}} : \operatorname{Fin} m' \to \mathbb{R}_{\ge 0}$. Let $\nu_j$ be left-invariant probability measures on the quotients of `euclideanSubspace (U j)` by `latticeSection`. Write $\mathcal{T}$ for the coefficient torus `CoefficientTorus U` with variables `LayerSamplerVariables G I n B`, where $G$ = `EnlargedPreparedCommonKernel m' J_alloc`, $I$ = `PreparedSamplerContinuous (prep.pad m')`, $n$ = `preparedSamplerTransverse (prep.pad m')` and $B$ = `EnlargedPreparedCommonSamplerBlock (prep.pad m') J_alloc` (all OpenAI's); assume $\mathcal{T}$ is compact with a Borel measurable structure, and let $\mu$ be a left-invariant probability measure on it. Similarly let the coefficient torus with one variable (`Fin (0+1)`) be compact Borel with a left-invariant probability measure $\mu_{\mathrm{rows}}$, and let `SiteTorus (Finset (Fin (0+1))) U` carry a Borel measurable structure.
--
--   **Scalar parameters and hypotheses.** Let $e, C_{\mathrm{primitive}}, C_{\mathrm{direct}}, \mathrm{extra}$ be natural numbers with $C_{\mathrm{primitive}} \ge 1$; reals $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, \mathrm{stageLog}, \mathrm{endpoint}, \mathrm{chartLog}, Q_\sigma, P_{\min}, \mathrm{requestedCoarse}, \mathrm{gainLog}, \mathrm{gain}, V_{\log}$, and natural numbers $L_{\min}, Q_{\mathrm{good}}$, with:
--   - $\mathrm{endpoint} \ge 0$; $\mathrm{chartLog} + 1 \le B_{\mathrm{struct}}$; $m' > 0$; $n_X > 0$; $|(\texttt{prep } j).\mathrm{Coord}| \le M$ for all $j \in \operatorname{Fin} m$;
--   - $B_{\mathrm{struct}} \ge 0$; $\mathrm{stageLog} \in [0, B_{\mathrm{struct}}]$; $Q_{\mathrm{stride}} \in [0, B_{\mathrm{struct}}]$; $Q_\sigma \ge 0$; $P_{\min} \ge 0$; $L_{\min} \le e^{P_{\min}}$; $\mathrm{gainLog} \ge 0$; $V_{\log} \ge 0$; $1 \le Q_{\mathrm{good}} \le e^{V_{\log}}$; $e^{-\mathrm{gainLog}} \le \mathrm{gain}$; $n_X \le B_{\mathrm{struct}}$; $\mathrm{gainLog} \le B_{\mathrm{struct}}$;
--   - $0 < \mathrm{stride}_i \le e^{Q_{\mathrm{stride}}}$ for all $i$;
--   - $C : \operatorname{Fin} m' \to \mathbb{R}$ with $0 \le C_j \le e^{\mathrm{chartLog}}$ and $\lVert \Phi_j^{-1}(v) \rVert \le C_j \lVert v \rVert$ for all $v$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`; $C^{\mathrm{fwd}} : \operatorname{Fin} m' \to \mathbb{R}_{\ge 0}$ with $\lVert \Phi_j(v) \rVert \le C^{\mathrm{fwd}}_j \lVert v \rVert$ and $C^{\mathrm{fwd}}_j \le e^{B_{\mathrm{struct}}}$;
--   - $V_{\mathrm{tail}, j} \le e^{B_{\mathrm{struct}}}$ and $0 \le$ `mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)` $\le V_{\mathrm{tail}, j}$ (the covolume of `latticeSection` divided by $\prod_i$ `basisAxisScale (b j) i`);
--   - `probabilityProfileLipschitz` $\le e^{B_{\mathrm{struct}}}$ and `normalizedSiteCutoffBound` $\le e^{B_{\mathrm{struct}}}$ (constants of OpenAI);
--   - `cells`, a nonempty finite set of column residue patterns (modulo `stride`) on $\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times \operatorname{Fin} n_X$;
--   - vector polynomials `poly j` in the variables $\operatorname{Fin} n_X$ with values in $\mathrm{Coord}_j \to \mathbb{R}$, of total degree at most $j+1$, with all coefficients in $U_j$;
--   - a real $R_{\mathrm{rank}}$ with `HasLayerSamplingRank (j+1) N R_rank (U j) (poly j)` for all $j$ (OpenAI's rank condition);
--   - `test` $: \mathbb{R}^{n_X} \to \mathbb{R}$ with $|\texttt{test}(x)| \le 1$ for all $x$ and $\mathrm{gain} \le \mathbb{E}_{x \in \texttt{integerBox N}}\, \texttt{test}(x)$ (uniform average over $\prod_i [0, N_i)$).
--
--   **Derived quantities.** The statement then introduces, by `let`, explicit quantities built from OpenAI's functions: the slot type $K$ = `PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff` $= \operatorname{Fin}(\mathrm{outerDepth}+1) \times \operatorname{Fin}(\mathrm{innerDepth}+1) \times \operatorname{Fin}(\mathrm{cutoff}+1) \times \mathrm{Bool}$ with degree map $k \mapsto$ its third component and anchor slot $k_{\mathrm{Model}}$; the schedule exponents $A$ (`preparedFiniteNestedSourceExponent`) and $C_{\mathrm{slice}}$; $\mathrm{forecastCap} = 1$; $Q_w = 2B_{\mathrm{struct}} + 2V_{\log} + 5(\mathrm{gainLog} + 8) + 24$; the detector polynomial $P_{\mathrm{detect}}$ = `preparedFiniteForwardDetectorPolynomial cutoff` and constants $C_{\mathrm{detect}}(k)$; per-slot precisions and work bounds `sourceU k`, `modelLog k`, `sliceLog k`; the model precision $u$ and work $p$; the dimension $p_{\mathrm{num}}$ = `enlargedPreparedCommonSamplerDimension m' M J_alloc`; the constant radius $R_j$ = `allocatedCommonProductRadius m' B_struct B_struct` with log $p_{\mathrm{Radius}}$; $D$ = `allocatedComparisonDimension m' p_num`; and further logs `pDetect`, `aDetect`, `detectionGain`, $P_k$, $P_{\mathrm{physical}}$, `target`, $E$, $P_\rho$, $P_{\mathrm{tail}}$, $P_{\mathrm{scale}}$, $T_{\mathrm{mod}}$, `lengthLogs`, $P_{\mathrm{seed}}$, $W$ = `physicalBadProductGap`, $P_{\mathrm{master}}$, `coarseTarget`, $P_{\mathrm{late}}$, `native`, $E_{\mathrm{conditional}}$, $\tau = e^{-(\mathrm{gainLog} + n_X + 8)}$, $\alpha(k)$, the certificate budgets `baseB0`, $P_{\mathrm{width}} = 4(P_{\mathrm{late}} + 8)^2$, $B_{\mathrm{cert}}$, $P_{\mathrm{good}}$, and the requirement levels `anchorRequired`, `conditionalRequired`, `detectorRequired` and $R_{\mathrm{req}}$ = `preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff B_struct anchorRequired conditionalRequired detectorRequired`; each is given by the exact formula in the Lean statement.
--
--   **Conclusion.** If $p_{\mathrm{num}} \le B_{\mathrm{struct}}$, $e^{R_{\mathrm{req}}} \le N_i$ for all $i$, and $e^{R_{\mathrm{req}}} \le R_{\mathrm{rank}}$, then: $R_j > 0$ for all $j$, and there exist a real $\sigma > 0$ and a `LayerSamplerScale B U b R (fun _ => σ)` named $S$ (OpenAI's structure containing a positive natural number `S.value`), such that all of the following hold:
--   1. $p_{\mathrm{Radius}} \ge 0$; $R_j \le 1$ and $R_j^{-1} \le e^{p_{\mathrm{Radius}}}$ for all $j$;
--   2. $\sigma \le 1$, $\sigma \le e^{-Q_\sigma}$, $\sigma^{-1} \le e^{P_{\mathrm{scale}}}$;
--   3. $L_{\min} \le \texttt{S.value} \le e^{\texttt{allocatedWitnessScaleLog}(P_{\mathrm{seed}}, Q_w)}$;
--   4. for all $j$ and $i$ with $\texttt{S.value}^{j+1} <$ `basisAxisScale (b j) i`: $8 \cdot \texttt{probabilityProfileLipschitz} \cdot W \le \bigl(\texttt{layerSamplerGapWidth B R (j, i)}/2\bigr) \cdot \texttt{basisAxisScale (b j) i} / \texttt{S.value}^{j+1}$;
--   5. for every slot $s$, `PreparedUniformDegreeGeometryAt B U b S (degree s) (Cdetect s) nX B_struct P_scale D (target s) (Pk s) (Prho s) Q_stride (pDetect s) p_Radius (aDetect s) (detectionGain s)`;
--   6. for every slot $k$, `PreparedUniformDegreeDirectScalarBounds` holds with the parameters of the Lean statement;
--   7. for every slot $k$, `PreparedScheduledDirectSourceAvailability` and `PreparedScheduledDegreeModelAvailability` hold for $S$, the canonical selection `enlargedPreparedCommonCanonicalSelection m' J_alloc (degree k)`, stride, $N$, $P_{\mathrm{detect}}$, the slot's precisions, $V_{\mathrm{tail}}$, $\tau$ (and $\mu$ for the second), with the parameters of the Lean statement;
--   8. `PreparedUniformDegreeProductiveSourceConclusion` holds for `prep.pad m'`, $U$, $b$, $S$ and the anchor-slot parameters (as in the Lean statement);
--   9. $2 \cdot$ `spatialTrimMargin τ N i` $\le N_i$ for all $i$; for every center $c \in \mathcal{T}$, `AllocatedExternalCandidateSampler B U b S hb o hR (fun _ => hσ) N poly hmem τ (exp (-P_late)) stride cells c` holds (call this family `Acandidate`); $e^{-P_{\mathrm{late}}} \le 1$; and `PreparedCenteredProductiveGoodCenterReadyConclusion` holds for `prep.pad m'`, $U, b, S, bW, \mu$, `poly`, stride, the widths `allocatedExternalCandidateWidths B U b S N τ (exp (-P_late))`, the bases of the sampler at center $0$, gainLog, gain, $Q_{\mathrm{good}}$, `preparedSpatialKernelBlocks m' M nX`, the family's law, $N$, `test`, and the following predicate of a center $c$: (a) for every slot $k$, `(Acandidate c).NativeDetection (degree k) (sliceLog k) (P_detect evaluated at pDetect k) (native budget of slot k) (α k)` (OpenAI's detection predicate); (b) the excess mass of the site law of the sampler at $c$ (on the physical box) over the uniform law on `integerBox N`, at level $4 \prod_j$ `earlyConstantDensityCap`, is at most $6 \cdot$ `positiveProjectionAccuracy` $E_{\mathrm{conditional}}$ (here `excessMass p q C` $= \sum_x \max(q(x) - C p(x), 0)$); and (c) for all `outerFront`, `outerInner` in $\operatorname{Fin}(\mathrm{outerDepth}+1)$, every $d \le \mathrm{cutoff}$ with $d \le \mathrm{innerDepth}$, and every real $p_{\mathrm{Input}} \in [0, \texttt{candidateNestedForwardSeed}(\dots, \texttt{outerFront})]$ with $p_{\mathrm{Input}} \le \texttt{candidateNestedForwardSeed}(\dots, \texttt{outerInner})$, there is a `DegreeSourceProfile d pInput e` of the sampler at $c$ (OpenAI's structure with a front and an inner profile) whose fields satisfy: inner `x` and inner `gainLog` both equal the seed for `outerInner`; front `u` and front `pModel` equal the stage-$0$ model precision and work for the seed of `outerFront`; front `nativeBudget` equals the native budget of the slot `(outerFront, 0, d, false)`; inner `Cprimitive` $= C_{\mathrm{primitive}}$; inner `scheduleExponent` $= A$; and inner `Csource` $=$ `preparedFiniteNestedSourceNativeExponent m' cutoff Cdirect`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedCanonicalInitializedRelativeSourceConclusion.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B294` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedCanonicalInitializedRelativeSourceConclusion.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B294

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
variable {nX : ℕ}
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

theorem exists_preparedFiniteNestedForwardCompleteFixedCenterSource_fullScalars_s2
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

    (e Cprimitive Cdirect extra : ℕ) (hprimitive : 1 ≤ Cprimitive)
    (Bstruct Qstride stageLog endpoint chartLog : ℝ)
    (hendpoint : 0 ≤ endpoint) (hchartLog : chartLog + 1 ≤ Bstruct)
    (Qσ Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < max m cutoff) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hstage : stageLog ∈ Set.Icc 0 Bstruct)
    (hQstride : Qstride ∈ Set.Icc 0 Bstruct)
    (hQσ : 0 ≤ Qσ) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin (max m cutoff) → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp chartLog)
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
    let stageCountConstant := AllocatedExternalCandidateSampler.degreeSourceCountConstants
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
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
    let native : K → ℝ := fun k =>
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope A stageCountConstant innerDepth
      (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
      Bstruct gainLog stageLog endpoint
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
          let _ : DecidableEq (Fin nX) := Classical.decEq _
          ((∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) ∧
          ∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
            ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ (pInput : ℝ),
            pInput ∈ Set.Icc 0 (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) →
            pInput ≤ candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct →
            ∃ profile : (Acandidate center).DegreeSourceProfile d pInput e,
              profile.inner.x = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.inner.gainLog = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.front.u = preparedFiniteForwardModelPrecision A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) gainLog stageLog ∧
              profile.front.pModel = preparedFiniteForwardWork A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) ∧
              profile.front.nativeBudget = native (outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
              profile.inner.Cprimitive = Cprimitive ∧
              profile.inner.scheduleExponent = A ∧
              profile.inner.Csource = preparedFiniteNestedSourceNativeExponent (max m cutoff) cutoff Cdirect) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
