-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineRowIdeal_cutoff_fixes_mean
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineRowIdeal_cutoff_fixes_mean
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:12:17.363371+00:00
-- url     : https://prove2.me/theorems/61a94089-7206-41f1-82ea-55114f33de2b
-- title:
--   The product site cutoff fixes the mean of masked covered profiles of the row ideal
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, $W_j = \mathbb Z^{J_j} \cap V_j$ (`latticeSection`), and bases $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a layer-sampler scale `S : LayerSamplerScale B U b R σ`; a finite type $\alpha$ with decidable equality and, for each $j$, a finite family $\mathrm{rowSets}_j$ of subsets of $\alpha$, with row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$ and $\mathrm{rows}_j$ the inclusion into $\mathrm{Finset}\,\alpha$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; the hypothesis $hb$ that the $\mathbb Z$-span of each $b_j$ is `projectedIntegerLattice V_j`; finite types $E_j$ and $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $E_j$; a positive natural number $d$; $r \in \mathbb R_{\ge 0}$ with $0 < r$; $R_j > 0$ and $\sigma_j > 0$ for all $j$; reals $T_j \ge 0$ with $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$ and $|\mathrm{rowSets}_j|\,T_j \le r$; and reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}v\| \le C_j\|v\|$ for all $v$ and $C_j\,(|I_j|+1)\,(2rR_j) \le 1/4$. Let grid be the predicate `allocatedGridAxis U b S.value`.
--
--   Assume $\sigma_j \le 1$ and `partitionedIdealRadius α m` $+ 1 \le T_j$ for all $j$ (where `partitionedIdealRadius α k` $= 1/4 + 2^{|\alpha|}(|\alpha|+1)^k$). Let $\rho \in \mathbb R_{\ge 0}$ with $0 < \rho \le 1$; let $\mathrm{center}, \mathrm{width}$ be real functions on `PrincipalAxisParameter (¬ grid)` with $|\mathrm{center}(i)| + |\mathrm{width}(i)| \le 1$; let $x : G \to $ `IntegerScalarCubeBox α S.value`; let $w$ be finite probability weights on a finite type $\Omega$ and $\mathrm{tuples} : \Omega \to$ `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; let $q$ be a natural number and $y \in$ `EuclideanJetLayers U rowTypes`. Put
--   $$\Phi(y) = \sum_{\omega} w(\omega)\,\texttt{allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples ω) q (allocatedRowSlicedIdeal B U b S rowSets ρ center width)}\ y.$$
--   Then `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y` $\cdot\, \Phi(y) = \Phi(y)$ in $\mathbb C$; here `allocatedProductSiteCutoff` is a product over subsets of $\alpha$ of complex site factors and `allocatedRowSlicedIdeal` is a real function, both defined by OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineRowIdeal_cutoff_fixes_mean` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineFiniteModelL2.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B143`, `OAIErdos3B171`, `OAIErdos3B172` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineFiniteModelL2.lean#L129

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B143
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B172

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

end Erdos3.VectorPolynomial

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
theorem allocatedAffineRowIdeal_cutoff_fixes_mean
    (hσ1 : ∀ j, σ j ≤ 1) (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (x : G → IntegerScalarCubeBox α S.value)
    {Ω : Type*} [Fintype Ω] (weights : FiniteProbabilityWeights Ω)
    (tuples : Ω → PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (y : EuclideanJetLayers U rowTypes) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr y *
      ((weights).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples u) q
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) =
      ((weights).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (tuples u) q
        (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y) : ℂ) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
