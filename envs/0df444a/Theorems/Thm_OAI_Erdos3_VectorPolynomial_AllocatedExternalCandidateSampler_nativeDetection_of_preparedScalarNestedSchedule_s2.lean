-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateSampler_nativeDetection_of_preparedScalarNestedSchedule_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:16:30.483718+00:00
-- url     : https://prove2.me/theorems/7db2affd-1853-44e7-bd9d-0ab0cc50b7ce
-- title:
--   The prepared scalar nested schedule gives native detection at every slot
-- statement:
--   Let $s, n_X \in \mathbb{N}$, and let the following data with an empty layer index set ($\mathrm{Fin}\ 0$) be given: types $I_0, J_0 : \mathrm{Fin}\ 0 \to \mathrm{Type}$, $n_0$, $B_0$, subspaces $U_0$, bases $b_0$, reals $R_0, \sigma_0$, `S₀ : LayerSamplerScale B₀ U₀ b₀ R₀ σ₀` over the group $\mathrm{Fin}$ (`scalarNativeDimension s`) (a structure bundling a positive natural number `S₀.value` with width and gap conditions; `scalarNativeDimension s` $= (s+1)(s+3)$), the lattice proof $hb_0$, orthonormal bases $o_0$, positivity proofs, $N : \mathrm{Fin}\ n_X \to \mathbb{N}$, vector polynomials $\mathrm{poly}_0$ with coefficients in $U_0$, reals $\tau, \xi_0$, a `CoefficientTorus` point $\mathrm{center}_0$, and the instances that each relevant lattice section is a $\mathbb{Z}$-lattice. Let `A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀ N poly₀ hmem₀ τ ξ₀ (fun _ => 1) {0} center₀` (a proposition bundling: all $N_x > 0$, $\tau > 0$, $\xi_0 > 0$, positive strides, a nonempty trimmed box, and positivity of the smooth residue mass and of the centered joint density mass, for stride $1$ and residue cell set $\{0\}$). Let $\mathrm{outerDepth}, \mathrm{innerDepth}, \mathrm{exponent}, C_{\mathrm{slice}}, C_{\mathrm{direct}} \in \mathbb{N}$, $\mathrm{constants} : \mathbb{N} \to \mathbb{N}$ and $B_{\mathrm{struct}}, \mathrm{gainLog}, \mathrm{stageLog}, \mathrm{extraLate}, p \in \mathbb{R}$, and assume: $3 \le \mathrm{exponent}$; $C_{\mathrm{slice}} + 1 \le \mathrm{exponent}$; `scalarNativeDimension s` $\le B_{\mathrm{struct}}$; $\mathrm{gainLog}, \mathrm{stageLog} \in [0, B_{\mathrm{struct}}]$; `probabilityProfileLipschitz` $\le e^{B_{\mathrm{struct}}}$ and `normalizedSiteCutoffBound` $\le e^{B_{\mathrm{struct}}}$ (two fixed nonnegative constants of OpenAI's construction); $2 \le p$; $n_X \le p \le B_{\mathrm{struct}}$; and $\tau = $ `unconditionedSpatialTrimFraction nX (exp (-p))` $= e^{-p}/(32(n_X + 1))$.
--
--   Define, as in the Lean `let` chain: the slot type $K = $ `PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s` $= \mathrm{Fin}(\mathrm{outerDepth}+1) \times \mathrm{Fin}(\mathrm{innerDepth}+1) \times \mathrm{Fin}(s+1) \times \mathrm{Bool}$; for $k \in K$ its `degree`, `stage`, `direct` flag and `seed` (from `preparedFiniteNestedForwardAllDegreeDegree`, `…Stage`, `…IsDirect`, and `preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct`); $\mathrm{sourceU}_k = $ `preparedFiniteForwardPairedSourcePrecision exponent Cdirect constants (stage k) (direct k) (seed k) gainLog stageLog`; $\mathrm{modelLog}_k = $ `preparedFiniteForwardWork exponent constants (stage k) (seed k)`; $\mathrm{sliceLog}_k = ($`preparedFiniteForwardParameter exponent constants (stage k) (seed k)` $+ C_{\mathrm{slice}})^{C_{\mathrm{slice}}}$; $\alpha = $ `preparedFiniteNestedForwardFixedCenterThreshold exponent constants Bstruct gainLog stageLog` (a real function on $K$); $P_{\mathrm{detect}} = $ `preparedFiniteForwardDetectorPolynomial s` (the natural-coefficient polynomial $X + c$ for OpenAI's offset $c$); $q = \max(s, 1)$; $\mathrm{count} = $ `scalarNativeDimension s`; and then, through OpenAI's budget functions `sampledSupportedSlicedDetectionConstant`, `allocatedCommonProductRadiusLog`, `allocatedComparisonDimension`, `allocatedModelTestLog`, `slicedDetectionGainLog`, `scalarKernelLogarithmicBudget`, `preparedFiniteScheduleLocalPhysical`, `coefficientErrorSpatialLog`, `affineProfileInputEnvelope`, `affineProfileToleranceEnvelope`, `preparedUniformDegreeScaleLog`, `allocatedAffineLengthLog`, `preparedFiniteScheduleLocalMaster`, `preparedFiniteScheduleDirectCoarse`, `preparedUniformDegreeDirectLate`, `preparedModularGeneralDetectorResources` and `preparedFiniteNestedSourceRequired`, exactly as written in the Lean statement, the per-slot detection constants, the late budget $P_{\mathrm{late}} = \sum_k \mathrm{localLate}_k$, the required detector resources, and the two reals
--   $$\mathrm{scaleFloor} = \max\Big(\mathtt{probabilityProfileLipschitz} + 8 + (D + 4) + p_{\mathrm{Radius}} + P_{\mathrm{scale}},\ \textstyle\sum_{k} \max(0, \mathrm{lengthLogs}_k)\Big),$$
--   $\mathrm{spatialFloor} = $ `preparedFiniteNestedSourceRequired exponent constants innerDepth outerDepth s Bstruct 0 0 detectorRequired`, where $D = $ `allocatedComparisonDimension q count` and $p_{\mathrm{Radius}} = $ `allocatedCommonProductRadiusLog q Bstruct Bstruct`. Assume $e^{\mathrm{scaleFloor}} \le$ `S₀.value` $\le e^{\mathrm{extraLate}}$ and $e^{\mathrm{spatialFloor}} \le N_i$ for every $i$. Then for every slot $k \in K$,
--   `A₀.NativeDetection (degree k) (sliceLog k) (Pdetect evaluated at allocatedModelTestLog (sourceU k) (modelLog k)) (preparedFiniteNestedSourceNative q (Fin (scalarNativeDimension s)) count nX Pdetect exponent Cdirect constants Bstruct count 0 gainLog stageLog Plate k) (α k)` holds.
--
--   `A.NativeDetection degree pSlice pTest pNative α` is the proposition: for every family, indexed by sampler paths $z$ and nonempty test types, of rational filtered nilmanifolds of step `degree` and niltests $V$ on them (all weights $1$), together with sets of sites forming common-stride boxes (positive step) that are dense in the sense of `IsDenseCommonStrideBox` with parameter $p_{\mathrm{Slice}}$, if every $V$ has `ComplexityLE pTest` and norm bound at most $1$, then OpenAI's `SampledSliceNativeDetection` holds for the conjugated test values with degree `degree`, native budget $p_{\mathrm{Native}}$ and threshold $\alpha$. `preparedFiniteNestedSourceNative … k` is the `nativeBudget` field of the detector resources for slot $k$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedScalarNestedPowerDetection.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B277` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedScalarNestedPowerDetection.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_preparedScalarNestedSchedule)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

namespace AllocatedExternalCandidateSampler
variable {s nX : ℕ}
    {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
    {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
    {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
    {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
    {R₀ σ₀ : Fin 0 → ℝ}
    {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
    {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
    {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
    {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
    {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
    {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
    {τ ξ₀ : ℝ}
    {center₀ : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]

theorem nativeDetection_of_preparedScalarNestedSchedule_s2
    (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
      N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀)
    (outerDepth innerDepth exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    (Bstruct gainLog stageLog extraLate p : ℝ)
    (hA : 3 ≤ exponent) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hnum : (scalarNativeDimension s : ℝ) ≤ Bstruct)
    (hg : gainLog ∈ Set.Icc 0 Bstruct) (hs : stageLog ∈ Set.Icc 0 Bstruct)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (hp : 2 ≤ p) (hX : (nX : ℝ) ≤ p) (hpB : p ≤ Bstruct)
    (htrim : τ = unconditionedSpatialTrimFraction nX (Real.exp (-p))) :
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth s
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let stage : K → ℕ := fun k => (preparedFiniteNestedForwardAllDegreeStage k).val
    let direct : K → Bool := preparedFiniteNestedForwardAllDegreeIsDirect
    let seed : K → ℝ := preparedFiniteNestedForwardAllDegreeSeed exponent constants Bstruct
    let sourceU := fun k : K => preparedFiniteForwardPairedSourcePrecision exponent Cdirect
      constants (stage k) (direct k) (seed k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork exponent constants (stage k) (seed k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter exponent constants (stage k) (seed k) + Cslice) ^ Cslice
    let α := preparedFiniteNestedForwardFixedCenterThreshold exponent constants Bstruct gainLog stageLog
    let Pdetect := preparedFiniteForwardDetectorPolynomial s
    let q := max s 1
    let count := scalarNativeDimension s
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let pRadius := allocatedCommonProductRadiusLog q Bstruct Bstruct
    let D := allocatedComparisonDimension q (count : ℝ)
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1))
      (Fin (scalarNativeDimension s)) (detectionGain k + pDetect k + 4)
    let Pphysical := fun k => preparedFiniteScheduleLocalPhysical q nX count 0 (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((q * 2 ^ (q + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope q D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail 0
    let Tmod := fun k => ((q + 1 : ℕ) : ℝ) * Pk k + nX * 0
    let lengthLogs := fun k => allocatedAffineLengthLog q D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius 0
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain 0
    let localLate := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k, localLate k
    let detectorRequired := fun k : K =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).required
    let scaleFloor := max (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale)
      (∑ k : K, max 0 (lengthLogs k))
    let spatialFloor := preparedFiniteNestedSourceRequired exponent constants innerDepth outerDepth s
      Bstruct 0 0 detectorRequired
    Real.exp scaleFloor ≤ S₀.value →
    (S₀.value : ℝ) ≤ Real.exp extraLate →
    (∀ i, Real.exp spatialFloor ≤ (N i : ℝ)) →
    ∀ k : K, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedFiniteNestedSourceNative q (Fin (scalarNativeDimension s)) count nX Pdetect
        exponent Cdirect constants Bstruct count 0 gainLog stageLog Plate k) (α k) := by
  sorry

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end
