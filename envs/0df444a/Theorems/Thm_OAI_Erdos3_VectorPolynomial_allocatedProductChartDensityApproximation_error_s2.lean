-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductChartDensityApproximation_error_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:21.865469+00:00
-- url     : https://prove2.me/theorems/6c85f6ed-bf0e-469e-a618-c14c5af7386a
-- title:
--   A uniform row-coordinate approximation of a density transfers to the full-grid prefactor versus the chart ideal approximation
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j<m$) finite types, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$, $J_j$ finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `b j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}(m) \to \mathbb{R}$, and `S : LayerSamplerScale B U b R σ`. Let $\alpha$ be a finite type with decidable equality, `rowSets j` a finite set of finite subsets of $\alpha$, and `rowTypes j` its subtype. Write `grid` = `allocatedGridAxis U b S.value` (a predicate on axes). Let $E_j$ be finite types, $x : G \to$ `IntegerScalarCubeBox α S.value`, $y_0$ an element of `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`, natural numbers $q$, $d \ge 1$, $\mathrm{period} \ge 1$, and $r \in \mathbb{R}_{\ge 0}$ with $r > 0$. Let `hb` state that the $\mathbb{Z}$-span of each `b j` is the projected integer lattice, $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$, and `bW j` $\mathbb{Z}$-bases (indexed by $E_j$) of the lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)`.
--
--   **Hypotheses.**
--   - For every $j$, `integerScalarLattice (rowTypes j) period` is contained in the range of the integer matrix `scalarKernelIntegerJet x (j+1) Subtype.val` (acting by matrix-vector multiplication).
--   - $M \ge 1$ is real, and for every $j$ and every $z$, $0 \le \mu_j(z) \le M$, where $\mu_j$ = `allocatedIntegerKernelMask B U b S x (fun j => Subtype.val) j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y₀) (fun j => Subtype.val) j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)`.
--   - $R_j > 0$; $C : \mathrm{Fin}(m) \to \mathbb{R}$ with $C_j \ge 0$; $\|\Phi_j^{-1}(v)\| \le C_j\|v\|$ for all $j, v$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)`; and for every $j$, $(|\texttt{rowSets}\ j| + 1)\cdot(|\mathrm{Finset}\ \alpha|\cdot(C_j((|I_j|+1)(2rR_j)))) \le 1/4$.
--
--   **Statement.** Let $K$ be a finite type, $a : K \to \mathbb{C}$, $f : K \to \mathrm{Finset}\ \alpha \to (\texttt{LayerSamplerAxis I n} \to \mathbb{R}) \to \mathbb{C}$, and $D$ a real function on real arrays indexed by $\mathcal{Q} = \Sigma_{a\,:\,\neg\mathrm{grid}(a)} \texttt{rowTypes}\ a.1$. Let $\varepsilon \ge 0$ and assume that for every $v$ in `AllocatedLongJetRows B U b S rowTypes`,
--   $$\Bigl\| \Bigl(\prod_{\mathbf{q} \in \mathcal{Q}} R_{\mathbf{q}.1.1}\Bigr)\cdot D\bigl(\texttt{allocatedLongJetRealCoordinates B U b S}\ v\bigr) - \sum_{k \in K} a_k \prod_{s \in \mathrm{Finset}\ \alpha} f_k(s)\bigl(\texttt{allocatedRowIdealCoordinates B U b S rowSets}\ v\ s\bigr)\Bigr\| \le \varepsilon,$$
--   where $R_{\mathbf{q}.1.1}$ is $R_j$ for $j$ the layer of the axis of $\mathbf{q}$. Then for every $y \in$ `EuclideanJetLayers U rowTypes`,
--   $$\bigl\| \texttt{allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ D}\ y - \texttt{allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f}\ y \bigr\| \le \bigl\| \nu^{-1} \bigr\|\cdot\bigl(M^{|\texttt{LayerSamplerAxis I n}|}\cdot \texttt{coefficientDeckPeriodCap rowTypes E period}\bigr)\cdot\varepsilon,$$
--   where $\nu$ = `allocatedProductIdealNormalizer B U b S rowSets` (a real number, cast to $\mathbb{C}$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error` (in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedGlobalMaskedDensity.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedGlobalMaskedDensity.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedProductChartDensityApproximation_error)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

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
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid

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
theorem allocatedProductChartDensityApproximation_error_s2 {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ v : AllocatedLongJetRows B U b S rowTypes,
      ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D (allocatedLongJetRealCoordinates B U b S v) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets v s)‖ ≤ ε)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ D y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
      ‖inverseNormalizer‖ *
        (M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period) * ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
