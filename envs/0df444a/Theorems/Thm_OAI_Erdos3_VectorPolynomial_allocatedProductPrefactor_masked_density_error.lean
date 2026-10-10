-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductPrefactor_masked_density_error
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductPrefactor_masked_density_error
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T08:54:33.784383+00:00
-- url     : https://prove2.me/theorems/c1f56c39-7bd9-4dcc-bda8-413fbae01b09
-- title:
--   A pointwise site expansion of the cut-off density bounds the masked prefactor error
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$ (rowTypes$_j$ is the subtype of $\mathrm{rowSets}_j$, rows$_j$ its inclusion); grid the predicate `allocatedGridAxis U b S.value`; finite types $E_j$; a point $x : G \to$ `IntegerScalarCubeBox α S.value`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; $q \in \mathbb N$ and natural numbers $d, \mathrm{period} \ne 0$; $r \in \mathbb R_{>0}$ (hr); $\mathbb Z$-span of $b_j$ equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; and $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`. Assume (hperiod) that for every $j$ the lattice $\mathrm{period}\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)`; let $M \ge 1$ (hM); and assume (hm) that for every $j$ and $z$, $0 \le \texttt{allocatedIntegerKernelMask B U b S x rows j q}\ (\mathrm{res}_j)\ z \le M$, where $\mathrm{res}_j$ is `allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (¬ grid) y₀)` reduced mod $q$. Let chart $=$ `mixedCoveredJetChart U o b hb bW d`, region $=$ `mixedCoveredJetRegion U o b d (j _ ↦ standardLatticeClosedQuarterBox (J j))`, cutoff $=$ `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr` (a product over sites of buffered site chart factors), and outputs $= \Sigma_{a\ \text{non-grid}}\,\mathrm{rowTypes}_{\mathrm{layer}(a)}$.
--
--   Assume $R_j > 0$ for all $j$. Let $K$ be a finite type, $a : K \to \mathbb C$, $f : K \to \mathrm{Finset}\,\alpha \to$ `MixedCoveredJetSource I (fun _ => Unit) E n d` $\to \mathbb C$, $D : \mathbb R^{\mathrm{outputs}} \to \mathbb R$, $\varepsilon \in \mathbb R$, and $z$ in `MixedCoveredJetSource I rowTypes E n d` lying in region, with (herr)
--   $$\Bigl\|\mathrm{cutoff}(\mathrm{chart}\,z)\cdot\Bigl(\prod_{t \in \mathrm{outputs}} R_{\mathrm{layer}(t)}\Bigr)\cdot D\bigl(\texttt{allocatedLongJetRealCoordinates B U b S}\,(\mathrm{split}\,z_1)_2\bigr) - \sum_k a_k\prod_s f\bigl(k, s, \texttt{mixedCoveredRowsSiteValue rowSets d z s}\bigr)\Bigr\| \le \varepsilon,$$
--   where $(\mathrm{split}\,z_1)_2$ is the non-grid part of `coefficientJetAxisSplit rowTypes I n grid` applied to the jet arrays $z_1$. Then
--   $$\Bigl\|\texttt{allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ D}\,(\mathrm{chart}\,z) - \sum_{\ell}\sum_k\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a}\ \ell\ k\cdot\prod_s\texttt{maskedSiteFactor}\ \lambda\ \ell\ f\ k\ s\ (\texttt{mixedCoveredRowsSiteValue rowSets d z s})\Bigr\|$$
--   $$\le \bigl\|\texttt{allocatedProductIdealNormalizer B U b S rowSets}^{-1}\bigr\|\cdot M^{|\texttt{LayerSamplerAxis I n}|}\cdot\texttt{coefficientDeckPeriodCap rowTypes E period}\cdot\varepsilon,$$
--   where the sum is over labels $\ell : \mathrm{Finset}\,\alpha \to (\prod_j (\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)}) \times (\prod_j (\mathbb Z/\mathrm{period})^{E_j})$; $\lambda$ reads off from a single-row source $v$ its integer jet entries and deck residues mod period; `maskedSiteFactor λ ℓ f k s v` is $f(k, s, v)$ if $\lambda(v) = \ell(s)$ and $0$ otherwise; and `coefficientDeckPeriodCap rowTypes E period` $= \prod_j \mathrm{period}^{|E_j|\cdot|\mathrm{rowTypes}_j|}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductPrefactor_masked_density_error` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedGlobalMaskedDensity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedGlobalMaskedDensity.lean#L131

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "factor" => allocatedBufferedSiteChartFactor B U b S o hb bW d r hr

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr

end Erdos3.VectorPolynomial

end

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
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "baseVolume" => (allocatedFullGridNaturalVolume B U b S rowSets *
  coveredJetArrayScale (O := rowTypes) U * ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)

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
local notation "cutoff" => allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr
local notation "mask" => allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

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

include hperiod hM hm in
theorem allocatedProductPrefactor_masked_density_error (hR : ∀ j, 0 < R j)
    {K : Type*} [Fintype K] (a : K → ℂ)
    (f : K → Finset α → MixedCoveredJetSource I (fun _ => Unit) E n d → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, f k s (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤ ε) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
        (D) (chart z) -
      ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ k,
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label k *
          ∏ s, maskedSiteFactor
            (fun _ v => (fun j i => ((v.1 j).2 i () : ZMod period),
              fun j i => ((v.2 j () i).val : ZMod period))) label f k s
              (mixedCoveredRowsSiteValue rowSets d z s)‖ ≤
      ‖inverseNormalizer‖ *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
