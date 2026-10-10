-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_global_masked_affine_ideal_approximation
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocated_global_masked_affine_ideal_approximation
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:31:11.198569+00:00
-- url     : https://prove2.me/theorems/89808613-3ad4-4c11-a69e-2326ad31ab22
-- title:
--   Finite chart expansion of the masked full-grid prefactor of the row-sliced ideal
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\, (I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; a finite type $\alpha$ with decidable equality and finite families $\mathrm{rowSets}_j$ of subsets of $\alpha$, with row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$ and $\mathrm{rows}_j$ the inclusion into $\mathrm{Finset}\,\alpha$; finite types $E_j$; a point $x : G \to $ `IntegerScalarCubeBox α L_S` (maps $\mathrm{Option}\,\alpha \to [-L_S, L_S) \cap \mathbb Z$); a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; natural numbers $q$, $d \neq 0$, $\mathrm{period} \neq 0$; a real $r > 0$ in $\mathbb R_{\ge 0}$; the hypothesis $hb$ that the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j` for every $j$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E_j$; the hypothesis $hperiod$ that for every $j$ the lattice $\mathrm{period}\cdot\mathbb Z^{\mathrm{rowTypes}_j}$ is contained in the range of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)`; a real $M \ge 1$ with $hm$: for every $j$ and $z$, $0 \le$ `allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x (y₀ restricted to grid axes) rows j (y₀ restricted to non-grid axes)) q) z` $\le M$, where the grid axes are those of `allocatedGridAxis U b L_S`; $R_j > 0$ for every $j$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1} v\| \le C_j \|v\|$ for all $v$; and the budget $(|\mathrm{rowSets}_j| + 1)\,|\mathcal P(\alpha)|\, C_j\,(|I_j| + 1)\, 2 r R_j \le 1/4$ for every $j$.
--
--   Let $\mathrm{center}, \mathrm{width}$ be real functions on `PrincipalAxisParameter (fun a => ¬ grid a)` with $|\mathrm{center}_i| + |\mathrm{width}_i| \le 1$ for all $i$; let $\delta \in \mathbb R_{\ge 0}$ with $0 < \delta \le 1$; and let $\varepsilon, p$ be reals with $\varepsilon > 0$, $p \ge 0$, $2\,$`allocatedRowSlicedSiteRadius rowSets` $\le e^{p}$, $\varepsilon^{-1} \le e^{p}$ and $\delta^{-1} \le e^{p}$. Put $\rho_s = $ `allocatedRowSlicedSiteRadius rowSets` (an explicit radius in $\mathbb R_{\ge 0}$), $\Lambda = |\texttt{LayerSamplerAxis I n}| \cdot \texttt{normalizedSiteCutoffBound} / (2\rho_s)$, $Q = $ `idealSiteLogBudget (card (Σ a, rowTypes a.1)) (card α) p` (an explicit real defined by OpenAI), $A = \exp\bigl(|\mathcal P(\alpha)|\,|\texttt{LayerSamplerAxis I n}|\,(4Q+8) + Q\bigr)$ and $\mathrm{maskCap} = M^{|\texttt{LayerSamplerAxis I n}|}\cdot$ `coefficientDeckPeriodCap rowTypes E period` $= M^{|\texttt{LayerSamplerAxis I n}|}\prod_j \prod_{E_j} \mathrm{period}^{|\mathrm{rowTypes}_j|}$. Write $K$ for the index type $\mathcal P(\alpha) \times \texttt{LayerSamplerAxis I n} \to \mathrm{Fin}\,k$ and $\mathcal L$ for the label type $(\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j E_j \to \mathbb Z/\mathrm{period})$.
--
--   Then there exists a natural number $k$ with $k \le e^{4Q+8}$ and $|K| \le \exp\bigl(|\mathcal P(\alpha)|\,|\texttt{LayerSamplerAxis I n}|\,(4Q+8)\bigr)$, and there exist $a : K \to \mathbb C$ and $f : K \to \mathcal P(\alpha) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ such that: $\sum_i \|a_i\| \le A$; $\|f_{i,s}(v)\| \le 1$ for all $i, s, v$; every $f_{i,s}$ is Lipschitz with constant $e^{|\texttt{LayerSamplerAxis I n}| + 6Q + 12} + \Lambda$; $f_{i,s}(v) = 0$ whenever $|v_j| > 2\rho_s$ for some axis $j$; $\sum_{\mathrm{label} : \mathcal P(\alpha) \to \mathcal L} \sum_i \|\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i}\| \le \|N^{-1}\|\cdot |\mathcal L|^{|\mathcal P(\alpha)|}\cdot \mathrm{maskCap}\cdot A$, where $N = $ `allocatedProductIdealNormalizer B U b S rowSets` (a real number, cast to $\mathbb C$); for all labels $\ell \in \mathcal L$, $i$, $s$, the function `allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period ℓ (f i s)` is measurable and bounded in norm by $1$ everywhere; the function `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f` is measurable; and for every $y$ in `EuclideanJetLayers U rowTypes` (families of points of the tori $V_j / (\mathbb Z^{J_j} \cap V_j)$ indexed by the rows),
--   $$\bigl\|\texttt{allocatedProductFullGridPrefactor}(\dots, \texttt{allocatedRowSlicedIdeal B U b S rowSets δ center width})(y) - \texttt{allocatedProductChartIdealApproximation}(\dots, a, f)(y)\bigr\| \le \|N^{-1}\|\cdot \mathrm{maskCap}\cdot \varepsilon,$$
--   where the prefactor is `allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ (allocatedRowSlicedIdeal B U b S rowSets δ center width)`. These are complex-valued functions on `EuclideanJetLayers U rowTypes` defined by OpenAI; the approximation is $\sum_{\mathrm{label}} \sum_k$ (masked coefficient) $\cdot \prod_s$ (masked site chart factor of $f_{k,s}$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocated_global_masked_affine_ideal_approximation` in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineAccurateSource.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B198` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedSupportedAffineAccurateSource.lean#L71

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

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

include hperiod hM hm hR hC hchart hbudget in
theorem exists_allocated_global_masked_affine_ideal_approximation
    (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
      (α := α) (fun a => ¬grid a) → ℝ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset α) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        ∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets δ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
