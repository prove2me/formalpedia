-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedFiniteScheduleProductiveFixedCenterSource_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T08:28:31.676991+00:00
-- url     : https://prove2.me/theorems/bc789ee0-5e12-4db0-b799-e85b0de03041
-- title:
--   Availability at every stage and a productive model give a ready candidate sampler family
-- statement:
--   The statement uses these section variables: $m, n_X, M \in \mathbb{N}$; types $X_0, J_0$; `prep : RankPreparationFamily X₀ J₀ m` (OpenAI's family of $m$ rank-preparation layers, layer $j$ having coordinate type $\mathrm{Coord}_j$); subspaces $U_j \subseteq \mathbb{R}^{\mathrm{Coord}_j}$; bases `basis j` of their orthogonal complements indexed by $\mathrm{Fin}$(`preparedSamplerTransverse prep j`) with $\mathbb{Z}$-span the projected integer lattice (`hb`); orthonormal bases $o_j$ of $U_j$ indexed by `PreparedSamplerContinuous prep`; reals $R_j, \sigma_j > 0$ (proofs `hR`, `hσ`); a `LayerSamplerScale` $S$ over OpenAI's enlarged prepared common sampler (kernel `EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))`, block `EnlargedPreparedCommonSamplerBlock prep …`) with radii $R$ and widths $\sigma$ (a structure bundling a positive natural number `S.value` with width and gap conditions); a type $\mathrm{Stage}$ with $\mathrm{degree} : \mathrm{Stage} \to \mathbb{N}$ and embeddings `selection k : Fin (degree k + 1) ↪` kernel; $\mathrm{stride}, N : \mathrm{Fin}\ n_X \to \mathbb{N}$; a polynomial $P_{\mathrm{detect}}$ with natural coefficients; real functions $\mathrm{sourceU}, \mathrm{modelLog}, \mathrm{sliceLog}, \alpha$ on $\mathrm{Stage}$; $V_{\mathrm{tail}} : \mathrm{Fin}\ m \to \mathbb{R}_{\ge 0}$; $\tau \in \mathbb{R}$; finite types $Q_j$ with $\mathbb{Z}$-bases $bW_j$ of the lattice sections $\mathbb{Z}^{\mathrm{Coord}_j} \cap U_j$ (assumed $\mathbb{Z}$-lattices); and a compact Borel structure on the `CoefficientTorus U` of the sampler variables.
--
--   Explicit data and hypotheses, in order: a stage $k_{\mathrm{Anchor}}$; reals $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{late}}, \mathrm{coarseTarget}$ and real functions $P_{\mathrm{master}}, P_{\mathrm{physical}}, p_{\mathrm{Gain}}$ on stages; `PreparedScheduledDirectSourceAvailability` at every stage $k$ (with `selection k`, the stage's logs and these budgets); a left-invariant probability measure $\mu$ on the coefficient torus and left-invariant probability measures $\nu_j$ on $U_j/(\text{lattice section})$; reals $P_{\mathrm{scale}}, D, \mathrm{target}, P_k, P_\rho, p_{\mathrm{Radius}}, E$ with `PreparedUniformDegreeDirectScalarBounds` and `PreparedUniformDegreeGeometryAt` at the anchor stage; `S.value` $\le e^{P_{\mathrm{late}}}$; $e^{-(2\,\mathrm{sourceU}_k + 4\,\mathrm{modelLog}_k + 7)} \le \alpha_k/2 \le 1$ for every $k$; $0 < \mathrm{stride}_i \le e^{Q_{\mathrm{stride}}}$; chart constants $0 \le C_j \le e^{P_{\mathrm{chart}}}$ and $C^{\mathrm{fwd}}_j \le e^{P_{\mathrm{chart}}}$ bounding the inverse and forward `normalizedOrthogonalChart` of $(U_j, \mathrm{basis}_j)$; $V_{\mathrm{tail},j} \le e^{P_{\mathrm{chart}}}$ and $0 \le$ `mixedDensityCovolumeRatio` $\le V_{\mathrm{tail},j}$; `probabilityProfileLipschitz`, `normalizedSiteCutoffBound` $\le e^{P_{\mathrm{chart}}}$; $0 < \tau \le 1/2$, $n_X\tau \le 1/2$ and $\tau^{-1} \le e^{P_{\mathrm{physical},k}}$ for all $k$; a real $\xi > 0$ with $\xi \le$ `normalizedTupleNarrowWidth …` (with OpenAI's `allocatedDetectedKernelCutoff` at threshold $\alpha_k/2$) for every $k$ and $\xi^{-1} \le e^{P_{\mathrm{late}}}$; a nonempty finite set `cells` of column residue patterns; vector polynomials $\mathrm{poly}_j$ of degree at most $j+1$ with coefficients in $U_j$ and `HasLayerSamplingRank (j+1) N Rrank (U j) (poly j)`; $e^{r_k} \le N_i$ and $e^{r_k} \le R_{\mathrm{rank}}$ for every stage, where $r_k$ is the `required` field of `preparedModularGeneralDetectorResources` for stage $k$; $e^{\mathtt{preparedConditionalExcessRequired}(m, P_{\mathrm{late}}, E)} \le N_i$ and $\le R_{\mathrm{rank}}$; the number of sampler variables is at most $P_{\mathrm{detect}}($`allocatedModelTestLog (sourceU k) (modelLog k)`$)$ for every $k$; productive data (an embedding `selectionProductive`, reals for its source, model, slice, $u$, $p$, forecast, master, gain and physical budgets, $B_0, \mathrm{gainLog}, \mathrm{gain}, P_{\mathrm{good}}$, $Q_{\mathrm{good}} \in \mathbb{N}$, an embedding `spatialEmbedding : Fin 2 × Fin nX ↪` kernel, and $P_{\mathrm{prod}}$) satisfying `SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface`; $\tau^{-1} \le e^{P_{\mathrm{physical}}^{\mathrm{prod}}}$; the analogous narrow-width bound on $\xi$ for the productive selection; size and rank bounds $e^{(\cdots)} \le N_i$ and $\le R_{\mathrm{rank}}$ for the productive requirement written in the Lean; and a function $\mathrm{test} : \mathbb{R}^{n_X} \to \mathbb{R}$ with $|\mathrm{test}| \le 1$, $e^{-\mathrm{gainLog}} \le \mathrm{gain}$ and $\mathrm{gain} \le \mathbb{E}_{x \in \prod_i[0,N_i)}\,\mathrm{test}(x)$.
--
--   Conclusion: there exist a proof that $2\,$`spatialTrimMargin τ N i` $\le N_i$ for all $i$ and a family `A : AllocatedExternalCandidateSamplerFamily … N poly hmem τ ξ stride cells` (for each center an `AllocatedExternalCandidateSampler`, a proposition bundling positivity and nonemptiness conditions) such that `PreparedCenteredProductiveGoodCenterReadyConclusion` holds for these data, the widths `allocatedExternalCandidateWidths … S N τ ξ`, the bases of `A 0`, $\mathrm{gainLog}, \mathrm{gain}, Q_{\mathrm{good}}$, `spatialEmbedding`, the law of `A`, $N$, the test, and the predicate on centers saying: for every stage $k$, `(A center).NativeDetection (degree k) (sliceLog k) (Pdetect at allocatedModelTestLog (sourceU k) (modelLog k))` with the stage's `nativeBudget` and threshold $\alpha_k$; and the excess mass of the site law of the candidate's physical box over the uniform law on $\prod_i[0,N_i)$, at level $4\prod_j$ `earlyConstantDensityCap` $(\ldots, R_j, V_{\mathrm{tail},j})$, is at most $6\,$`positiveProjectionAccuracy E`.
--
--   The named predicates and budget functions are OpenAI's definitions and are not unfolded here.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteNestedForwardCanonicalFixedCenterSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B285`, `OAIE3v2B290` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedFiniteNestedForwardCanonicalFixedCenterSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleProductiveFixedCenterSource)

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

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
attribute [local instance] OAI.Erdos3.VectorPolynomial.productiveFixedSourceFinDecidableEq
variable (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
variable (basis : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]

theorem exists_preparedFiniteScheduleProductiveFixedCenterSource_s2
    (kAnchor : Stage)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Pscale D target Pk Prho pRadius E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m (degree kAnchor) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect)
      Pchart Pscale D target Pk Prho Qstride (Pmaster kAnchor) Plate (pGain kAnchor)
      (Pphysical kAnchor) coarseTarget pRadius (sourceU kAnchor) (modelLog kAnchor) (sliceLog kAnchor))
    (geometryAt : PreparedUniformDegreeGeometryAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S (degree kAnchor)
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (sourceU kAnchor) (modelLog kAnchor))
      pRadius (2 * sourceU kAnchor + 4 * modelLog kAnchor + 7) (pGain kAnchor))
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) (selection k)
      (allocatedDetectedKernelCutoff (degree k) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hsizeConditional : ∀ i, Real.exp (preparedConditionalExcessRequired m Plate E) ≤ (N i : ℝ))
    (hRankConditional : Real.exp (preparedConditionalExcessRequired m Plate E) ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (selectionProductive : Fin (0 + 1) ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))))
    (sourceProductive modelProductive sliceProductive uProductive pProductive forecastProductive : ℝ)
    (PmasterProductive pGainProductive PphysicalProductive : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ)
    (hProductiveSource : SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      prep U basis hR hσ S selectionProductive stride N Pdetect sourceProductive modelProductive sliceProductive
      Vtail τ uProductive pProductive forecastProductive hb o bW μ
      Pchart Qstride PmasterProductive Plate pGainProductive PphysicalProductive coarseTarget
      B0 gainLog gain Pgood Qgood spatialEmbedding Pprod)
    (hτInvProductive : τ⁻¹ ≤ Real.exp PphysicalProductive)
    (hξSmallProductive : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selectionProductive
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog sourceProductive modelProductive) (allocatedModelTestLog sourceProductive modelProductive) (forecastAugmentedUnitThreshold uProductive pProductive (Real.exp (sliceProductive * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastProductive / 2))
      PphysicalProductive coarseTarget)
    (hsizeProductive : ∀ i, Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ (N i : ℝ))
    (hRankProductive : Real.exp (max
      (max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).required ((max ((preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m 0) (0 + 1) PmasterProductive Plate)).Pproj E + preparedCenteredMarginalExponent m) ^
        preparedCenteredMarginalExponent m)) (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
        ((Pprod + preparedModularGeneralProductivityExponent m) ^
          preparedModularGeneralProductivityExponent m))) ≤ Rrank)
    (test : (Fin nX → ℝ) → ℝ)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))
    : ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    ∃ A : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S hb o hR hσ N poly hmem τ ξ stride cells,
      PreparedCenteredProductiveGoodCenterReadyConclusion (m := m) (nX := nX) (M := M)
        prep U basis S bW hb o hR hσ μ poly hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U basis S N τ ξ) (A 0).bases
        gainLog gain Qgood spatialEmbedding A.law N test (fun center =>
    (∀ k, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) (A center).integerBox_nonempty).excessMass
        ((A center).law.siteLaw ((A center).physicalBox
          ((hξSmall kAnchor).trans (min_le_left _ _)) hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
