-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductChartIdealApproximation_eq_mixed
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductChartIdealApproximation_eq_mixed
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:18:54.322256+00:00
-- url     : https://prove2.me/theorems/7e9f2168-597b-474e-94dd-f6affbb15bc2
-- title:
--   On the covered region the chart ideal approximation equals its mixed-source form
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$ (rowTypes$_j$ is the subtype of $\mathrm{rowSets}_j$); finite types $E_j$; a point $x : G \to$ `IntegerScalarCubeBox α S.value`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; $q \in \mathbb N$ and natural numbers $d, \mathrm{period} \ne 0$; $r \in \mathbb R_{>0}$ (hr); $\mathbb Z$-span of $b_j$ equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; and $C : \mathrm{Fin}\,m \to \mathbb R$ with $C_j \ge 0$ (hC), $\|(\texttt{normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)})^{-1}v\| \le C_j\|v\|$ for all $v$ (hchart), and $(|\mathrm{rowSets}_j| + 1)\cdot 2^{|\alpha|}\cdot C_j(|I_j|+1)\cdot 2rR_j \le 1/4$ (hbudget), for all $j$. Let chart $=$ `mixedCoveredJetChart U o b hb bW d` and region $=$ `mixedCoveredJetRegion U o b d (j _ ↦ standardLatticeClosedQuarterBox (J j))`.
--
--   Let $K$ be a finite type, $a : K \to \mathbb C$, $f : K \to \mathrm{Finset}\,\alpha \to \mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C$, and let $z$ in `MixedCoveredJetSource I rowTypes E n d` (mixed real/integer jet arrays together with deck residues mod $d$) lie in region. Then
--   $$\texttt{allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f}\,(\mathrm{chart}\,z) = \sum_{\ell}\sum_{k \in K}\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a}\ \ell\ k\cdot\prod_{s \in \mathrm{Finset}\,\alpha}\texttt{allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f}\ \ell\ k\ s\ (\texttt{mixedCoveredRowsSiteValue rowSets d z s}),$$
--   the sum over labels $\ell : \mathrm{Finset}\,\alpha \to (\prod_j (\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)}) \times (\prod_j (\mathbb Z/\mathrm{period})^{E_j})$, where `mixedCoveredRowsSiteValue rowSets d z s` is the single-row source obtained from $z$ by the row-restricted site matrices at $s$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductChartIdealApproximation_eq_mixed` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedRecenteredIdealError.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedRecenteredIdealError.lean#L96

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hR hC hchart hbudget in
theorem allocatedProductChartIdealApproximation_eq_mixed {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f (chart z) =
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, allocatedProductMaskedIdealSiteFactor B U b S d period r hr hb o bW f label k s
            (mixedCoveredRowsSiteValue rowSets d z s) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
