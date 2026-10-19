-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateSampler_nativeDetection_of_emptyLayer_sampler_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:24:41.096516+00:00
-- url     : https://prove2.me/theorems/22921b4d-d5b6-4766-ad09-06eaf3ef6918
-- title:
--   Native detection transfers from an empty-layer sampler to the zero-layer sampler
-- statement:
--   Work in OpenAI's layer-sampler setting with zero layers, with the following implicit: finite types $G$, $X$; families $I_j$, $J_j$ of finite types, $n_j$ of natural numbers and $B_a$ of finite types, all indexed by $\mathrm{Fin}\,0$; subspaces $U_j$, bases $b_j$, reals $R_j,\sigma_j$ with proofs $hR$, $h\sigma$ of positivity, a `LayerSamplerScale` $S$ for $B,U,b,R,\sigma$; $hb$; orthonormal bases $o_j$; $N:X\to\mathbb{N}$; vector polynomials $\mathrm{poly}_j$ with coefficients in $U_j$ ($hm$); reals $\tau,\xi$; a point $\mathrm{center}$ of `CoefficientTorus U`; and the $\mathbb{Z}$-lattice instances. Let $A$ be an `AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ (fun _ => 1) {0} center` (stride $1$ in every coordinate and the single residue pattern $0$; a proposition bundling positivity facts, with path and site types and laws defined by OpenAI). Let $q$ be a natural number and, implicitly, $I'_j$, $J'_j$ ($j<q$) finite types that are all empty, $n'_j$ natural numbers with every $\mathrm{Fin}\,n'_j$ empty (so $n'_j=0$), finite types $B'_a$, subspaces $U'_j$, bases $b'_j$, reals $R'_j,\sigma'_j$ with positivity proofs $hR'$, $h\sigma'$, a `LayerSamplerScale` $S'$ (over the same $G$), $hb'$, orthonormal bases $o'_j$, vector polynomials $\mathrm{poly}'_j$ with coefficients in $U'_j$ ($hm'$), a real $\xi'$, a point $\mathrm{center}'$, and the $\mathbb{Z}$-lattice instances. Let $A_{\mathrm{source}}$ be an `AllocatedExternalCandidateSampler B' U' b' S' hb' o' hR' hσ' N poly' hm' τ ξ' (fun _ => 1) {0} center'` (same $N$ and $\tau$), and assume $S'.\mathrm{value}=S.\mathrm{value}$. Let $\mathrm{degree}$ be a natural number and $p_{\mathrm{Slice}},p_{\mathrm{Test}},p_{\mathrm{Native}},\alpha$ reals. If `Asource.NativeDetection degree pSlice pTest pNative α` holds, then `A.NativeDetection degree pSlice pTest pNative α` holds; here `NativeDetection` is OpenAI's proposition that every family of rational-nilmanifold niltests on dense common-stride slices (complexity at most $p_{\mathrm{Test}}$, norm bound at most $1$, density parameter $p_{\mathrm{Slice}}$) satisfies `SampledSliceNativeDetection … degree pNative α`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedZeroLayerDetectionFromEmptySampler.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B304` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedZeroLayerDetectionFromEmptySampler.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.nativeDetection_of_emptyLayer_sampler)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304

section

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

theorem nativeDetection_of_emptyLayer_sampler_s2
    {q : ℕ} {I' J' : Fin q → Type}
    [∀ j, Fintype (I' j)] [∀ j, Fintype (J' j)]
    [∀ j, IsEmpty (I' j)] [∀ j, IsEmpty (J' j)]
    {n' : Fin q → ℕ} [∀ j, IsEmpty (Fin (n' j))]
    {B' : LayerSamplerAxis I' n' → Type} [∀ a, Fintype (B' a)]
    {U' : ∀ j, Submodule ℝ (J' j → ℝ)}
    {b' : ∀ j, Basis (Fin (n' j)) ℝ (euclideanSubspace (U' j))ᗮ}
    {R' σ' : Fin q → ℝ} {S' : LayerSamplerScale (G := G) B' U' b' R' σ'}
    {hb' : ∀ j, span ℤ (Set.range (b' j)) = projectedIntegerLattice (euclideanSubspace (U' j))}
    {o' : ∀ j, OrthonormalBasis (I' j) ℝ (euclideanSubspace (U' j))}
    {hR' : ∀ j, 0 < R' j} {hσ' : ∀ j, 0 < σ' j}
    {poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ)}
    {hm' : ∀ j e, coefficients (poly' j) e ∈ U' j}
    {ξ' : ℝ} {center' : CoefficientTorus (K := LayerSamplerVariables G I' n' B') U'}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J' j)) (euclideanSubspace (U' j)))]
    (Asource : AllocatedExternalCandidateSampler B' U' b' S' hb' o' hR' hσ'
      N poly' hm' τ ξ' (fun _ : X => 1) {0} center')
    (hvalue : S'.value = S.value)
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (hsource : Asource.NativeDetection degree pSlice pTest pNative α) :
    A.NativeDetection degree pSlice pTest pNative α := by
  sorry

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end
