-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerKernelPMF_split_scale_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:55:13.045316+00:00
-- url     : https://prove2.me/theorems/8896397d-fb85-4828-bff8-51010abf7810
-- title:
--   The allocated integer kernel law equals the image of a split-scale coefficient law under the joined kernel and nonkernel jet matrix
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$, $J_j$ be finite types, $O_j$ a type and $n_j$ a natural number; let $B$ assign a finite type to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$ and `basis j` a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (that subspace in the Euclidean space $\mathbb{R}^{J_j}$; defined by OpenAI). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\alpha$ be a type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\ \alpha \to [-\texttt{S.value}, \texttt{S.value}) \cap \mathbb{Z}$). Write `grid` for OpenAI's predicate `allocatedGridAxis U basis S.value` on axes and `sides` for `allocatedPrincipalSides B U basis S`; let $u$ be a principal integer tuple on the grid axes (in `PrincipalAxisTuples grid sides`). Let `rows j` $: O_j \to$ finite subsets of $\alpha$.
--
--   Fix $j \in \operatorname{Fin} m$ and $i \in \operatorname{Fin} n_j$ with $\sigma_j \le 1$ (hσ1) and $\texttt{S.value}^{\texttt{layerTailDegree } m + 1} < h$ (henormous), where $h$ = `basisAxisScale (basis j) i` $= \lceil \lVert \texttt{basis}_j(i) \rVert^{-1} \rceil$ and `layerTailDegree m` $= m(2^{m+1} + 1)$. Let `centers` = `allocatedIntegerProfileCenters B R j i` and `widths` = `allocatedIntegerProfileWidths B R σ j i` (OpenAI's profile centers and widths, functions on `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`), and let `reindex` = `allocatedKernelCoefficientEquiv B j`, OpenAI's bijection from `BoundedIntegerExponent G (j+1)` $\sqcup$ `AllocatedNonkernelCoefficient B j` onto `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` (kernel and nonkernel coefficients). Let $f$ = `affineProductProfile (centers ∘ reindex) (widths ∘ reindex)`, i.e. $f(y) = \prod_d w_d^{-1} \phi\bigl((y_d - c_d)/w_d\bigr)$ with $\phi$ = OpenAI's `smoothProbabilityProfile`. Let the scale $\Sigma$ on the joined index type be: on a kernel coefficient $e$, `kernelJetCoefficientScale G (j+1) S.value h e` $= h / \texttt{S.value}^{|e|}$; on a nonkernel coefficient $d$, $h / \texttt{monomialScale (layerSamplerBox B U basis S) (allocatedNonkernelExponent B j d)}$ (here `monomialScale T e` $= \prod_k T_k^{e_k}$ and `layerSamplerBox` gives OpenAI's box side of each sampler variable).
--
--   Assume (hZ) $\sum_{z} f\bigl(z / \Sigma\bigr) > 0$, the sum over all integer vectors $z$ on the joined index type, with $z/\Sigma$ taken coordinatewise (`coefficientWeightSum f Σ`). Then for every principal integer tuple $v$ on the non-grid axes,
--   `allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous`
--   (OpenAI's probability mass function on $O_j \to \mathbb{Z}$: the image of OpenAI's enormous-profile law under multiplication by the partitioned jet matrix) equals
--   `coefficientImagePMF A f _ Σ _ _ hZ`,
--   the image, under $z \mapsto A z$, of the probability mass function on integer vectors $z$ with weights proportional to $f(z/\Sigma)$, where $A$ is the block matrix $\bigl[\, \texttt{scalarKernelIntegerJet x (j+1) (rows j)} \ \big|\ \texttt{allocatedNonkernelJetMatrix B U basis S x u rows j v} \,\bigr]$ with columns indexed by the kernel coefficients followed by the nonkernel coefficients (both integer matrices with rows $O_j$, defined by OpenAI). The remaining arguments of `coefficientImagePMF` are proofs that $f \ge 0$, that $\Sigma > 0$, and that $f$ vanishes outside a ball.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedIntegerKernelComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B194` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedIntegerKernelComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelPMF_split_scale)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (i : Fin (n j)) (s : O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id s).det ≠ 0)
variable (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "nonkernelScale" => fun d => height / monomialScale (layerSamplerBox B U basis S)
  (allocatedNonkernelExponent B j d)
local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedIntegerKernelPMF_split_scale_s2
    (hZ : 0 < coefficientWeightSum (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
      (Sum.elim kernelScale nonkernelScale))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous =
      coefficientImagePMF
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (Sum.elim kernelScale nonkernelScale)
        (Sum.rec (kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) heightPos)
          (fun _d => div_pos heightPos (monomialScale_pos _
            (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k)) _)))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d))) hZ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
