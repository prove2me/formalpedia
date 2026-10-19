-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductFullGridPrefactor_site_masks_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:58:33.019101+00:00
-- url     : https://prove2.me/theorems/93d2e6bf-64b8-4bd6-8e29-f3fd3183c1d6
-- title:
--   On the mixed covered jet region, the allocated product full-grid prefactor factors as a site cutoff times a clipped site mask times a normalized test value
-- statement:
--   **Setting.** Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $b_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and $S$ a `LayerSamplerScale B U b R σ` (a structure defined by OpenAI, with natural-number value `S.value`). Let $\alpha$ be a finite type with decidable equality, $\mathrm{rowSets} : \mathrm{Fin}\,m \to \mathrm{Finset}(\mathrm{Finset}\,\alpha)$ with $\mathrm{rowTypes}_j$ the subtype of $\mathrm{rowSets}_j$ and $\mathrm{rows}_j : \mathrm{rowTypes}_j \to \mathrm{Finset}\,\alpha$ the inclusion; let $E_j$ be finite types, $x : G \to$ `IntegerScalarCubeBox α S.value`, $y_0$ an element of `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`, and $q, d, \mathrm{period}$ natural numbers with $d \ne 0$ and $\mathrm{period} \ne 0$. Let $r > 0$ be a nonnegative real (hypothesis $h_r$). Assume (hypothesis $h_b$) that for each $j$ the $\mathbb{Z}$-span of $b_j$ is the projected integer lattice `projectedIntegerLattice` of $U_j$; let $o_j$ be an orthonormal basis of $U_j$ indexed by $I_j$ and $bW_j$ a $\mathbb{Z}$-basis, indexed by $E_j$, of the section of the standard lattice $\mathbb{Z}^{J_j}$ by $U_j$. Let $f$ be a real-valued function of real vectors indexed by pairs (non-grid axis $a$, element of $\mathrm{rowTypes}$ of the layer of $a$), where the grid axes are those with `allocatedGridAxis U b S.value a`.
--
--   Let $\mathrm{chart}$ = `mixedCoveredJetChart U o b h_b bW d` (a map from `MixedCoveredJetSource I rowTypes E n d` to jet layers, defined by OpenAI) and $\mathrm{region}$ = `mixedCoveredJetRegion U o b d Ω` with $\Omega_{j,t}$ the closed quarter box $\{v \in \mathbb{R}^{J_j} : |v_i| \le 1/4 \text{ for all } i\}$ for all $j, t$.
--
--   **Statement.** Assume that for every $j$ the lattice $\mathrm{period} \cdot \mathbb{Z}^{\mathrm{rowTypes}_j}$ is contained in the image of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)` acting on integer vectors. Let $z \in \mathrm{region}$. Then
--   $$\texttt{allocatedProductFullGridPrefactor B U b S rowSets d r h\_r x h\_b o bW q y₀ f}\,(\mathrm{chart}\ z) = \texttt{allocatedProductSiteCutoff B U b S rowSets o h\_b bW d r h\_r}\,(\mathrm{chart}\ z) \cdot \frac{\mathrm{mask} \cdot f\bigl(\texttt{allocatedLongJetRealCoordinates B U b S}\ ((\mathrm{split}\ z_1).2)\bigr)}{V \cdot \kappa \cdot \prod_a \texttt{allocatedLongJetOutputScale B U b S}\ a}$$
--   (the real fraction on the right cast to $\mathbb{C}$), where:
--   - $\mathrm{mask}$ = `allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period` applied to the labelling that sends each subset $s$ to the pair of residue vectors modulo $\mathrm{period}$ read off from the two components of `mixedCoveredRowsSiteValue rowSets d z s` (the integer coordinates of the first component, and the values of the second component);
--   - $\mathrm{split}$ = `coefficientJetAxisSplit rowTypes I n grid`, applied to the first component $z_1$ of $z$;
--   - $V$ = `allocatedFullGridNaturalVolume B U b S rowSets`, $\kappa$ = `coveredJetArrayScale U` (for the row types `rowTypes`), and the product runs over all axes $a$ with output scales `allocatedLongJetOutputScale` (for `rowTypes`).
--
--   All functions named in backticks are defined by OpenAI: `allocatedProductFullGridPrefactor` is the prefactor of the allocated product model on the full grid, `allocatedProductSiteCutoff` a site cutoff factor, and `allocatedClippedPrefactorSiteMask` a clipped site mask built from the integer kernel masks.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductPrefactorMasks.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductPrefactorMasks.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedProductFullGridPrefactor_site_masks)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

namespace OAI

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
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid

variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

theorem allocatedProductFullGridPrefactor_site_masks_s2
    (hperiod : ∀ j, integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀ f (chart z) =
      allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) *
        ((allocatedClippedPrefactorSiteMask B U b S rowSets x y₀ q d period
          (fun s => (fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).1 j).2 i () : ZMod period),
            fun j i => (((mixedCoveredRowsSiteValue rowSets d z s).2 j () i).val : ZMod period))) *
          f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) /
          (allocatedFullGridNaturalVolume B U b S rowSets * coveredJetArrayScale (O := rowTypes) U *
            ∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a) : ℝ) : ℂ) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
