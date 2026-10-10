-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductSiteCutoff_fixes_source
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_fixes_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T01:46:24.74118+00:00
-- url     : https://prove2.me/theorems/32ab6b96-67aa-4c04-a32e-18062d8b95c8
-- title:
--   The product site cutoff fixes the whole masked covered profile
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets}_j$ finite sets of finite subsets of $\alpha$; write $\mathrm{rowTypes}_j$ for the subtype of members of $\mathrm{rowSets}_j$ and rows for the inclusions $\mathrm{rowTypes}_j \to \mathrm{Finset}\,\alpha$. Let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$; assume ($h_b$) that the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$; let $E_j$ be finite types and $bW_j$ a $\mathbb Z$-basis indexed by $E_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace); let $d \ne 0$ be a natural number and $r > 0$ a nonnegative real. Assume $R_j > 0$ and $\sigma_j > 0$ for all $j$. Let $T_j$ be reals with $T_j \ge 0$, $|$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$| \cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$, and $|\mathrm{rowSets}_j|\,T_j \le r$ for all $j$. Let $C_j \ge 0$ be reals such that the inverse of the continuous linear equivalence `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` satisfies $\|\cdot^{-1}(v)\| \le C_j\|v\|$ for all $v$, and $C_j\bigl((|I_j|+1)(2 r R_j)\bigr) \le 1/4$, for all $j$. Let grid be `allocatedGridAxis U b S.value` (a predicate on `LayerSamplerAxis I n`). Then: assuming $\sigma_j \le 1$ for all $j$, for every $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), every $y_0 \in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`, every $q \in \mathbb N$, every $f : \mathbb R^{\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}} \mathrm{rowTypes}_{a.1}} \to \mathbb R$ such that $f(v) \ne 0$ implies $|v_{(a,t)}| \le T_{a.1} R_{a.1}$ for all $a$ with $\neg\,\mathrm{grid}\,a$ and all $t \in \mathrm{rowTypes}_{a.1}$, and every $y \in$ `EuclideanJetLayers U rowTypes`,
--   $$\texttt{allocatedProductSiteCutoff}\ B\ U\ b\ S\ \mathrm{rowSets}\ o\ h_b\ bW\ d\ r\ h_r\ y \cdot P(y) = P(y),$$
--   where $P(y)$ is the real number `allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y` cast to $\mathbb C$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_fixes_source` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductIdealCutoff.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B140`, `OAIErdos3B143`, `OAIErdos3B157`, `OAIErdos3B172` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductIdealCutoff.lean#L146

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B140
import Definitions.Def_OAIErdos3B143
import Definitions.Def_OAIErdos3B157
import Definitions.Def_OAIErdos3B172

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical Matrix

variable {α : Type*} [DecidableEq α]

namespace VectorPolynomial

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (d : ℕ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

include hT hsource hradius hC hchart hbudget in
theorem allocatedProductSiteCutoff_fixes_source (hσ1 : ∀ j, σ j ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ)
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hf : ∀ v, f v ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : rowTypes a.val.1,
      |v ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
        (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ) =
      (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y₀ q f y : ℂ) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
