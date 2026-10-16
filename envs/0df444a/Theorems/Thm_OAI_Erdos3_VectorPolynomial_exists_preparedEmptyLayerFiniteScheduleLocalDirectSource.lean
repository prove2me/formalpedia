-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
-- name    : OAI.Erdos3.VectorPolynomial.exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-16T01:50:06.652221+00:00
-- url     : https://prove2.me/theorems/b195f748-93bd-420a-9c2b-0c56bae3c99c
-- title:
--   Empty-layer radii and width exist giving scheduled direct sources for a finite schedule
-- statement:
--   Let $m, s, n_X$ be natural numbers; $G$ a finite type with decidable equality; $I_j, J_j$ ($j \in \mathrm{Fin}\,m$) finite types that are all empty, and $n : \mathrm{Fin}\,m \to \mathbb N$ with every $\mathrm{Fin}(n_j)$ empty (so all layers are empty); $B_a$ finite types with decidable equality for $a \in$ `LayerSamplerAxis I n`; $U_j \le \mathbb R^{J_j}$ subspaces and $b_j$ bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`; $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$; a polynomial $P_{\mathrm{detect}} \in \mathbb N[x]$; $V_{\mathrm{tail}} : \mathrm{Fin}\,m \to \mathbb R_{\ge 0}$; a real $\tau$; finite types $Q_j$; a proof $hb$ that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))`; orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$, indexed by $Q_j$, of the lattice sections `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (assumed `IsZLattice`); a finite type $K$, $\mathrm{degree} : K \to \mathbb N$ and embeddings $\mathrm{selection}_k : \mathrm{Fin}(\mathrm{degree}_k + 1) \hookrightarrow G$. Assume $m > 0$, $s \le m$, $\mathrm{degree}_k \le s$ for all $k$, and $(s+1)(s+3) \le |G|$. Let $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, Q_\sigma, \mathrm{requestedCoarse}, \mathrm{extraLate}$ be reals and $u_{\mathrm{src}}, \mathrm{modelLog}, \mathrm{sliceLog} : K \to \mathbb R$, with $B_{\mathrm{struct}} \ge 0$, $|G| \le B_{\mathrm{struct}}$, $u_{\mathrm{src},k} \ge 0$, $\mathrm{modelLog}_k \ge 0$, $\mathrm{sliceLog}_k \le \mathrm{modelLog}_k$, $|G| \le e^{\mathrm{modelLog}_k}$ for all $k$, $Q_{\mathrm{stride}} \ge 0$ and $Q_\sigma \ge 0$.
--
--   Define (all named functions are real-valued expressions defined by OpenAI): $\mathrm{count} = |$`LayerSamplerVariables G I n B`$|$; $C_{\mathrm{detect},k} =$ `sampledSupportedSlicedDetectionConstant (degree k) Pdetect`; $R_j =$ `allocatedCommonProductRadius m Bstruct Bstruct` for every $j$; $p_{\mathrm{radius}} =$ `allocatedCommonProductRadiusLog m Bstruct Bstruct`; $D =$ `allocatedComparisonDimension m |G|`; $p_{D,k} =$ `allocatedModelTestLog (u_src k) (modelLog k)` $= 2u_{\mathrm{src},k} + 5\,\mathrm{modelLog}_k + 12$; $a_k = 2u_{\mathrm{src},k} + 4\,\mathrm{modelLog}_k + 7$; $g_k =$ `slicedDetectionGainLog (degree k) Cdetect_k count p_D,k p_D,k a_k`; $P_{k,k} =$ `scalarKernelLogarithmicBudget (Fin (degree k + 1)) G (g_k + p_D,k + 4)`; $P_{\mathrm{phys},k} =$ `preparedFiniteScheduleLocalPhysical m nX count Qstride P_k,k`; $\mathrm{target}_k = g_k + 40 +$ `coefficientErrorSpatialLog P_phys,k`; $E_k = \mathrm{target}_k + D \cdot m 2^{m+1} P_{k,k} + 5$; $P_{\rho,k} = 2\,$`affineProfileInputEnvelope D canonicalSublevelCutoffLip canonicalTransitionLip E_k (p_D,k + 2)` $+ 2$; $P_{\mathrm{tail},k} =$ `affineProfileToleranceEnvelope m D (D(D+1) + D·D + D + 1) canonicalSublevelCutoffLip canonicalTransitionLip E_k (p_D,k + 2)`; $P_{\mathrm{scale}} =$ `preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ` $= D + p_{\mathrm{radius}} + \sum_{k \in K} P_{\mathrm{tail},k} + Q_\sigma$; $T_{\mathrm{mod},k} = (m+1) P_{k,k} + n_X Q_{\mathrm{stride}}$; $\ell_k =$ `allocatedAffineLengthLog m D Pscale P_ρ,k P_k,k target_k (p_D,k + 2) T_mod,k`; $P_{\mathrm{master},k} =$ `preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride P_phys,k u_src,k modelLog_k P_ρ,k target_k g_k`; $\mathrm{coarseTarget} =$ `preparedFiniteScheduleDirectCoarse g requestedCoarse`; $\mathrm{late}_k =$ `preparedUniformDegreeDirectLate P_master,k Pscale P_phys,k coarseTarget extraLate`; and $P_{\mathrm{late}} = \sum_{k \in K} \mathrm{late}_k$.
--   Then there exist a proof $hR$ that $R_j > 0$ for all $j$ and a real $\sigma > 0$ such that $0 \le p_{\mathrm{radius}}$; $R_j \le 1$ and $R_j^{-1} \le e^{p_{\mathrm{radius}}}$ for all $j$; $\sigma \le 1$, $\sigma \le e^{-Q_\sigma}$ and $\sigma^{-1} \le e^{P_{\mathrm{scale}}}$; and for every `LayerSamplerScale` $S$ for $(B, U, b, R, \text{the constant } \sigma)$ over $G$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities) with $e^{\ell_k} \le S.\mathrm{value}$ for all $k$ and $S.\mathrm{value} \le e^{\mathrm{extraLate}}$: for every $k$,
--   `PreparedUniformDegreeDirectScalarBounds m (degree k) nX count Cdetect_k Bstruct Pscale D target_k P_k,k P_ρ,k Qstride P_master,k Plate g_k P_phys,k coarseTarget pRadius u_src,k modelLog_k sliceLog_k` (a structure of inequalities among these reals);
--   `PreparedUniformDegreeGeometryAt B U b S (degree k) Cdetect_k nX Bstruct Pscale D target_k P_k,k P_ρ,k Qstride p_D,k pRadius a_k g_k` (a geometric condition defined by OpenAI); and `PreparedScheduledDirectSourceAvailability` for $B, U, b, S, hR, \sigma$, $\mathrm{selection}_k$, $\mathrm{stride}$, $N$, $P_{\mathrm{detect}}$, $u_{\mathrm{src},k}$, $\mathrm{modelLog}_k$, $\mathrm{sliceLog}_k$, $V_{\mathrm{tail}}$, $\tau$, $hb$, $o$ and the reals $B_{\mathrm{struct}}, Q_{\mathrm{stride}}, P_{\mathrm{master},k}, P_{\mathrm{late}}, g_k, P_{\mathrm{phys},k}, \mathrm{coarseTarget}$ (the proposition that for every $\alpha$ with $e^{-a_k} \le \alpha \le 1$ OpenAI's interface `PreparedModularGeneralDirectDetectionFreeTrimPreparedSharedWidthInterface` holds).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_preparedEmptyLayerFiniteScheduleLocalDirectSource` in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedEmptyLayerFiniteScheduleLocalDirectSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B1347`, `OAIErdos3B1372` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedEmptyLayerFiniteScheduleLocalDirectSource.lean#L11

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B1347
import Definitions.Def_OAIErdos3B1372

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
    {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0) (τ : ℝ)
    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {K : Type} [Fintype K] (degree : K → ℕ)
    (selection : ∀ k, Fin (degree k + 1) ↪ G)
    (hm : 0 < m) (hsm : s ≤ m) (hdegree : ∀ k, degree k ≤ s)
    (hcapacity : (s + 1) * (s + 3) ≤ Fintype.card G)
    (Bstruct Qstride Qσ requestedCoarse extraLate : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hB : 0 ≤ Bstruct) (hnum : (Fintype.card G : ℝ) ≤ Bstruct)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card G : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride) (hQσ : 0 ≤ Qσ) :
    let count := Fintype.card (LayerSamplerVariables G I n B)
    let pnum : ℝ := Fintype.card G
    let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (detectionGain k + pDetect k + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun k => ((m + 1 : ℕ) : ℝ) * Pk k + nX * Qstride
    let lengthLogs := fun k => allocatedAffineLengthLog m D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let localLate := fun k : K => preparedUniformDegreeDirectLate
      (Pmaster k) Pscale (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k : K, localLate k
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      ∀ S : LayerSamplerScale (G := G) B U b R (fun _ => σ),
        (∀ k, Real.exp (lengthLogs k) ≤ S.value) →
        (S.value : ℝ) ≤ Real.exp extraLate →
        (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
          (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
        (∀ k, PreparedUniformDegreeGeometryAt B U b S (degree k) (Cdetect k) nX
          Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (pDetect k) pRadius
          (aDetect k) (detectionGain k)) ∧
        (∀ k, PreparedScheduledDirectSourceAvailability
          (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
