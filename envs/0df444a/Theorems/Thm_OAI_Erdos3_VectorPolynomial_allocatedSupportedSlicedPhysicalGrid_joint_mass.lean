-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGrid_joint_mass
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGrid_joint_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T16:37:16.906985+00:00
-- url     : https://prove2.me/theorems/63b900b4-1f92-44d0-9832-e5f9dc44a53d
-- title:
--   The joint physical grid law of distinct grid axes is the product of the marginals
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q\in\mathbb N$; write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)` (triples $\langle a,b,v\rangle$ with $b\in B(a)$ and $v<j+1$ for $a=\langle j,\_\rangle$). Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ for all $t$ (`hsubset`; `allocatedPrincipalSides` assigns a positive natural number to each index, via `layerSamplerSides`), and assume (`hcell`) that the event `principalResidueLabel q y = r` (coordinatewise reduction mod $q$) has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Let $A$ be a finite type, `selected` $\colon A\to\Sigma_j\,\mathrm{Fin}\,n_j$ injective (`hselected`) with `allocatedGridAxis U basis S.value ⟨(selected a).1, inr (selected a).2⟩` for every $a$ (`hgrid`; an axis $\langle j,\mathrm{inr}\,i\rangle$ is a grid axis when `basisAxisScale (basis j) i` $\le\texttt{S.value}^{\texttt{layerTailDegree}\ m+1}$), `rows` $\colon A\to$ `Finset (Finset α)`, and $x\colon G\to$ `IntegerScalarCubeBox α S.value`. Then for every $z$ assigning an integer to each $a\in A$ and each element of `rows a`, the probability of $z$ under `allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x` (as a real number) equals $\prod_{a}$ of the probability of $z_a$ under `allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell (selected a).1 (selected a).2 (rows a) x`. Both are PMFs obtained by drawing $y$ from `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step c … hH hsubset q r hcell` and then pushing the `allocatedLayerIntegerPMFs` of the selected axes forward under `integerMatrixImagePMF` of a `boundedCoefficientJetMatrix` built from $x$ and $y$; the joint one takes the dependent product over $a\in A$ inside the draw of $y$, the marginal one is for a single axis $(j,i)$ and row set.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGrid_joint_mass` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedGridMarginal.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedGridMarginal.lean#L90

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable {A : Type*} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (rows : A → Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)

variable (hselected : Function.Injective selected)
variable (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value
  ⟨(selected a).1, Sum.inr (selected a).2⟩)

include hselected hgrid in
theorem allocatedSupportedSlicedPhysicalGrid_joint_mass (z : ∀ a, rows a → ℤ) :
    (allocatedSupportedSlicedPhysicalJointPMF B U basis hR hσ S q r H step c hH hsubset hcell selected rows x z).toReal =
      ∏ a, (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell
        (selected a).1 (selected a).2 (rows a) x (z a)).toReal := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
