-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernel_image_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:42:09.229162+00:00
-- url     : https://prove2.me/theorems/daae4522-b0a8-411f-a101-186677ef8a39
-- title:
--   The image of a continuous allocated coefficient row under a nonsingular integer jet matrix has the allocated continuous kernel density
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For each $j < m$ let $I_j$ and $J_j$ be finite types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $\mathrm{basis}_j$ a real basis, indexed by $\{0, \dots, n_j - 1\}$, of the orthogonal complement of the Euclidean subspace given by $U_j$. For each layer sampler axis $a$ (a pair $(j, c)$ with $j < m$ and $c \in I_j \sqcup \{0,\dots,n_j-1\}$, OpenAI's `LayerSamplerAxis I n`) let $B_a$ be a finite type. Let $R, \sigma : \{0, \dots, m-1\} \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a layer sampler scale (OpenAI's `LayerSamplerScale B U basis R σ`, whose main field is a positive natural number `S.value`). Fix $j < m$ and $i \in I_j$, and assume $\sigma_j \le 1$.
--
--   Let $\alpha$ and $O$ be finite types with decidable equality. Let $x : G \to$ `IntegerScalarCubeBox α S.value` (each $x_g$ assigns to every element of $\mathrm{Option}\,\alpha$ an integer in $[-\texttt{S.value}, \texttt{S.value})$). Let `grid` be the predicate `allocatedGridAxis U basis S.value` on axes (OpenAI: false on the axes $(j', c)$ with $c \in I_{j'}$, and on $(j', i')$ with $i' < n_{j'}$ it says `basisAxisScale (basis j') i'` $\le \texttt{S.value}^{\,\texttt{layerTailDegree}\ m + 1}$) and `sides` = `allocatedPrincipalSides B U basis S` (OpenAI side lengths for the principal tuple indices). Let $u$ be a principal axis tuple for the grid axes with these sides and $v$ a principal axis tuple for the non-grid axes with these sides (OpenAI's `PrincipalAxisTuples`: for each principal index $(a, b, r)$ with $a$ in the respective set of axes, $b \in B_a$, $r < \deg a$, a point of the integer cube $\mathrm{Option}\,\alpha \to [-\mathrm{side}, \mathrm{side}) \cap \mathbb{Z}$). Let $\mathrm{rows} : O \to \mathrm{Finset}\,\alpha$ and let $s$ be an embedding of $O$ into the set of exponent vectors on $G$ of total degree at most $j+1$. Assume that the square submatrix, with columns selected by $s$, of `scalarKernelIntegerJet x (j+1) rows` (OpenAI's integer jet matrix of the monomials of degree at most $j+1$ along the integer affine cube built from $x$, with row sets $\mathrm{rows}(o)$) has nonzero determinant.
--
--   Let $\lambda$ = `allocatedCoefficientAxisLaw B U basis hR hσ S (j, i)`, the law (defined by OpenAI) of the row of real coefficients at the continuous axis $(j, i)$: a product, over the exponent vectors $d$ of total degree at most $j+1$ in the layer sampler variables, of affine coefficient measures with OpenAI's allocated centers and widths. Let $M$ be the integer matrix `integerMappedJetMatrix (fun d => d) input fixedInteger rows (principalTupleIntegers v)` (OpenAI), with rows indexed by $O$ and columns by those exponent vectors $d$: its $(o, d)$ entry is $\sum_{T \subseteq \mathrm{rows}(o)} (-1)^{|\mathrm{rows}(o) \setminus T|}\, y_T^{\,d}$, where $y_T$ is the point of the integer affine cube whose coordinates are read, through OpenAI's partition `partitionedPrincipalInput` of the sampler variables into the spatial variables $G$, the grid principal parameters and the non-grid principal parameters, from the integers $x_g(\cdot)$, the entries of $u$ and the entries of $v$ respectively. Then the image of $\lambda$ under the linear map $a \mapsto M a$ (with $M$ cast to a real matrix) equals the measure with density $\max(\rho, 0)$ with respect to Lebesgue measure on $\mathbb{R}^{O}$ (OpenAI's `realDensityMeasure volume ρ`), where
--   $$\rho = \texttt{allocatedContinuousKernelDensity B U basis S j i x u rows s hA}\ (\bar v),$$
--   $\bar v$ = `principalTupleNormalized … v` being the entries of $v$ each divided by its side length, and `allocatedContinuousKernelDensity` an explicit density defined by OpenAI (an affine selected-jet density built from the normalized pivot of the nonsingular submatrix, the remaining columns, the real normalized data of $x$ and $u$, and the allocated continuous centers and widths at $(j, i)$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law` (in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelScaleWithCutoff.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B176` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelScaleWithCutoff.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedContinuousKernel_image_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B176

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable (j : Fin m) (i : I j)

local notation "centers" => allocatedContinuousProfileCenters (G := G) B R j i
local notation "widths" => allocatedContinuousProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) 1

theorem allocatedContinuousKernel_image_law_s2 (hσ1 : σ j ≤ 1)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inl i⟩).map
      (fun a => (integerMappedJetMatrix
        (fun d : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) => d.val)
        input fixedInteger rows (principalTupleIntegers v)).map (Int.cast : ℤ → ℝ) *ᵥ a) =
      realDensityMeasure volume
        (allocatedContinuousKernelDensity B U basis S j i x u rows s hA
          (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
