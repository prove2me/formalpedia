-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedEmptyLayerFiniteScheduleCandidateDetection_s2
-- name    : OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:23:12.889986+00:00
-- url     : https://prove2.me/theorems/b4facd9a-f2be-4216-91b2-db9783e4ae6f
-- title:
--   Native detection at every schedule point for an external candidate sampler with empty layers
-- statement:
--   Let $m, n_X$ be natural numbers; $G$ a finite type with decidable equality; $I_j$, $J_j$ ($j < m$) finite types that are all **empty**; $n_j$ natural numbers with every $\{0,\dots,n_j-1\}$ empty (that is, $n_j = 0$); $B(a)$, for each layer-sampler axis $a$, a finite type (all types in universe $0$); $U_j \subseteq \mathbb{R}^{J_j}$ subspaces; $b_j$ bases (indexed by $\{0,\dots,n_j-1\}$) of the orthogonal complement of $U_j$ with $hb$: the $\mathbb{Z}$-span of $b_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))`; $o_j$ orthonormal bases (indexed by $I_j$) of $U_j$; `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` assumed to be a $\mathbb{Z}$-lattice in $U_j$; reals $R_j > 0$, $\sigma_j > 0$; and a `LayerSamplerScale B U b R σ` $S$ (all defined by OpenAI).
--
--   Let $K$ be a type (the schedule), $\mathrm{degree} : K \to \mathbb{N}$, embeddings $\mathrm{selection}_k : \{0, \dots, \mathrm{degree}(k)\} \hookrightarrow G$, functions $\mathrm{stride}, N : \{0,\dots,n_X - 1\} \to \mathbb{N}$, a polynomial $P_{\mathrm{detect}}$ with natural-number coefficients, functions $\mathrm{sourceU}, \mathrm{modelLog}, \mathrm{sliceLog}, \alpha, P_{\mathrm{master}}, P_{\mathrm{physical}}, p_{\mathrm{gain}} : K \to \mathbb{R}$, and reals $\tau, \xi, P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{late}}, \mathrm{coarseTarget}$. Assume:
--   - for every $k$, `PreparedScheduledDirectSourceAvailability` holds for the data $B, U, b, S, hR, h\sigma$, $\mathrm{selection}_k$, stride, $N$, $P_{\mathrm{detect}}$, source $\mathrm{sourceU}(k)$, model log $\mathrm{modelLog}(k)$, slice log $\mathrm{sliceLog}(k)$, tail $1$, $\tau$, $hb$, $o$ and the parameters $P_{\mathrm{chart}}, Q_{\mathrm{stride}}, P_{\mathrm{master}}(k), P_{\mathrm{late}}, p_{\mathrm{gain}}(k), P_{\mathrm{physical}}(k), \mathrm{coarseTarget}$ (an OpenAI-defined proposition: for every $\alpha' \in [e^{-(2\,\mathrm{sourceU} + 4\,\mathrm{modelLog} + 7)}, 1]$ a prepared shared-width direct-detection interface holds);
--   - $e^{-(2\,\mathrm{sourceU}(k) + 4\,\mathrm{modelLog}(k) + 7)} \le \alpha(k)/2 \le 1$ for every $k$;
--   - $\mathrm{stride}(i) \le e^{Q_{\mathrm{stride}}}$ for every $i$;
--   - `probabilityProfileLipschitz` $\le e^{P_{\mathrm{chart}}}$ and `normalizedSiteCutoffBound` $\le e^{P_{\mathrm{chart}}}$ (constants defined by OpenAI);
--   - $\tau^{-1} \le e^{P_{\mathrm{physical}}(k)}$ for every $k$, $\tau \le 1/2$, and $n_X \tau \le 1/2$;
--   - for every $k$, $\xi \le$ `normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k) M_k (Pphysical k) coarseTarget`, where $M_k$ = `allocatedDetectedKernelCutoff (degree k) G |LayerSamplerVariables G I n B| Pdetect ℓ_k ℓ_k (α k / 2)` and $\ell_k$ = `allocatedModelTestLog (sourceU k) (modelLog k)`; and $\xi^{-1} \le e^{P_{\mathrm{late}}}$;
--   - `cells` is a finite set of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride`; $\mathrm{poly}_j$ are `VectorPolynomial (Fin nX) ℝ (J j → ℝ)` with all coefficients in $U_j$;
--   - for every $k$ and $i$, $\exp(\texttt{required}) \le N(i)$, where `required` is the field of `preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate`;
--   - for every $k$, $\lvert\texttt{LayerSamplerVariables G I n B}\rvert \le P_{\mathrm{detect}}(\ell_k)$ (the polynomial evaluated at the real $\ell_k$);
--   - `center` is a point of `CoefficientTorus (K := LayerSamplerVariables G I n B) U`, and `AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hmem τ ξ stride cells center` holds (OpenAI structure of positivity and nonemptiness facts about the sampler), call it $A$.
--
--   Then for every $k \in K$, `A.NativeDetection (degree k) (sliceLog k) (Pdetect(ℓ_k)) nativeBudget_k (α k)` holds, where $\mathrm{nativeBudget}_k$ is the `nativeBudget` field of the same detector resources as above. (`NativeDetection degree pSlice pTest pNative α` is an OpenAI-defined proposition: for every family of niltests of the given degree on rational filtered nilmanifolds, with complexity at most pTest and norm bound at most $1$, tested on dense common-stride slices at density level pSlice, the sampled slice native detection `SampledSliceNativeDetection` holds with budget pNative and threshold $\alpha$.)
--
--   Lean: `OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection` (in `lean/OAI/Combinatorics/Progressions/Estimates/PreparedScalarFiniteScheduleCandidateDetection.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B285` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/PreparedScalarFiniteScheduleCandidateDetection.lean (declaration OAI.Erdos3.VectorPolynomial.preparedEmptyLayerFiniteScheduleCandidateDetection)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedEmptyLayerFiniteScheduleCandidateDetection_s2
    {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    {K : Type} (degree : K → ℕ) (selection : ∀ k, Fin (degree k + 1) ↪ G)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (sourceU modelLog sliceLog α : K → ℝ) (τ ξ : ℝ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (Pchart Qstride : ℝ) (Pmaster : K → ℝ) (Plate : ℝ)
    (Pphysical : K → ℝ) (coarseTarget : ℝ) (pGain : K → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
      (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := fun _ => 1) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hmem τ ξ stride cells center) :
    ∀ k, A.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
