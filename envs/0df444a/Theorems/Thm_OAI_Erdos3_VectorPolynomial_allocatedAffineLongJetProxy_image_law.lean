-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLongJetProxy_image_law
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_image_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:37:37.24972+00:00
-- url     : https://prove2.me/theorems/4ff9247b-874f-4214-b36f-177c63e8f1da
-- title:
--   The affine long-jet proxy is the image density of the Boolean and coefficient sources
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`; finite types $O_j$ with decidable equality and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that the square integer matrices obtained by restricting the columns of `scalarKernelIntegerJet x (j+1) (rows j)` to $s_j$ have nonzero determinant ($hA$); and real functions $\mathrm{center}, \mathrm{width}$ on `PrincipalAxisParameter (¬ grid)`, where grid is the predicate `allocatedGridAxis U basis S.value`. Assume $\sigma_j \le 1$ for all $j$. Then the push-forward of the product measure `jointBooleanSource (layerSamplerDegree I n on non-grid axes)` $\times$ `unitCoefficientSource (ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid)` (measures defined by OpenAI; the second is Lebesgue measure with density `smoothProductProfile`) under the map
--   $$(p_1, p_2) \mapsto \texttt{allocatedNormalizedLongJetMap B U basis S x u rows}\ \bigl(i \mapsto \mathrm{center}(i) + \mathrm{width}(i)\,p_1(i)\bigr)\ p_2$$
--   equals Lebesgue measure with density $\max(f, 0)$, where $f = $ `allocatedAffineLongJetProxy B U basis S x u rows s hA center width` is a real function on $\Sigma_{a\ \text{non-grid}}\, O_{\mathrm{layer}(a)} \to \mathbb R$ defined by OpenAI (`realDensityMeasure volume f`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_image_law` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B136` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean#L78

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B136

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

include hR hσ in
theorem allocatedAffineLongJetProxy_image_law (hσ1 : ∀ j, σ j ≤ 1) :
    ((jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)).prod
      (unitCoefficientSource activeCoefficient)).map
      (fun p => allocatedNormalizedLongJetMap B U basis S x u rows
        (fun i => center i + width i * p.1 i) p.2) =
      realDensityMeasure volume (allocatedAffineLongJetProxy B U basis S x u rows s hA center width) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
