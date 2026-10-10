-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRowSlicedIdeal_measurable
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRowSlicedIdeal_measurable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:16:36.443334+00:00
-- url     : https://prove2.me/theorems/c45db777-8ab1-4a35-8a2c-317390b938d6
-- title:
--   The allocated row-sliced ideal density is measurable
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets}_j$ ($j \in \mathrm{Fin}\,m$) finite sets of finite subsets of $\alpha$. Let grid be `allocatedGridAxis U b S.value` (a predicate on `LayerSamplerAxis I n`) and input the finite type `PrincipalAxisParameter (¬grid)` (with block types $B$ and degrees `layerSamplerDegree I n`, $a \mapsto a.1+1$). Assume $R_j > 0$ for all $j$, and let $\rho > 0$ be a nonnegative real and center, width $: \mathrm{input} \to \mathbb R$. Then the function `allocatedRowSlicedIdeal B U b S rowSets ρ center width`, a real-valued function on $\mathbb R^{\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}} \mathrm{rowSets}_{a.1}}$ (index set: pairs of an axis $a$ with $\neg\,\mathrm{grid}\,a$ and a member of $\mathrm{rowSets}_{a.1}$), is measurable.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRowSlicedIdeal_measurable` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineFiniteModelL2.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B144` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineFiniteModelL2.lean#L24

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))

theorem allocatedRowSlicedIdeal_measurable (hR : ∀ j, 0 < R j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (center width : input → ℝ) :
    Measurable (allocatedRowSlicedIdeal B U b S rowSets ρ center width) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
