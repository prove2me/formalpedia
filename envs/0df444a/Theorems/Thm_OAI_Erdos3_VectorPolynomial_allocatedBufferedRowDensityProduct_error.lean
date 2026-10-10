-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedRowDensityProduct_error
-- name    : OAI.Erdos3.VectorPolynomial.allocatedBufferedRowDensityProduct_error
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:34:27.355018+00:00
-- url     : https://prove2.me/theorems/12d7a19b-63b6-4a83-a8d1-c3c7419137d7
-- title:
--   Inserting the product site cutoff preserves a row-density product approximation
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, $W_j = \mathbb Z^{J_j} \cap V_j$ (`latticeSection`), and bases $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a layer-sampler scale `S : LayerSamplerScale B U b R σ`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; the hypothesis $hb$ that the $\mathbb Z$-span of each $b_j$ is `projectedIntegerLattice V_j`; finite types $E_j$ and $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $E_j$; a positive natural number $d$; $r \in \mathbb R_{\ge 0}$ with $0 < r$; a finite type $\alpha$ with decidable equality and, for each $j$, a finite family $\mathrm{rowSets}_j$ of subsets of $\alpha$ with row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$; the hypothesis $R_j > 0$; reals $C_j \ge 0$ with $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}v\| \le C_j\|v\|$ for all $v$; and the budget $(|\mathrm{rowSets}_j| + 1)\cdot 2^{|\alpha|}\cdot C_j\,(|I_j|+1)\,(2rR_j) \le 1/4$ for every $j$. Let grid be the predicate `allocatedGridAxis U b S.value`, chart $=$ `mixedCoveredJetChart U o b hb bW d`, region $=$ `mixedCoveredJetRegion U o b d` for the closed quarter boxes $\{x : |x_i| \le 1/4\}$ at every row, split $=$ `coefficientJetAxisSplit rowTypes I n grid` (a measurable equivalence separating grid and non-grid axis rows), and cutoff $=$ `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr`.
--
--   Let $K$ be a finite type, $a : K \to \mathbb C$, $f : K \to \mathrm{Finset}\,\alpha \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$, $D$ a real function on $(\Sigma_{a\ \text{non-grid}}\, \mathrm{rowTypes}_{\mathrm{layer}(a)}) \to \mathbb R$, $\varepsilon$ a real number, and $z$ a point of `MixedCoveredJetSource I rowTypes E n d` lying in region. Write $\Pi = \prod_q R_{\mathrm{layer}(q)}$ over the pairs $q$ of a non-grid axis and a row, $\zeta = (\mathrm{split}\ z_1)_2$ (the non-grid rows of the real and integer part of $z$), and $\Delta = \Pi\cdot D(\texttt{allocatedLongJetRealCoordinates B U b S}\ \zeta)$. Assume
--   $$\Bigl\|\Delta - \sum_k a_k \prod_{s \subseteq \alpha} f_{k,s}\bigl(\texttt{allocatedRowIdealCoordinates B U b S rowSets}\ \zeta\ s\bigr)\Bigr\| \le \varepsilon.$$
--   Then
--   $$\Bigl\|\mathrm{cutoff}(\mathrm{chart}\ z)\cdot\Delta - \sum_k a_k \prod_{s \subseteq \alpha} \texttt{allocatedBufferedSiteChartFactor B U b S o hb bW d r hr}\ (f_{k,s})\ \bigl(\texttt{coveredRowsSiteValue rowSets U}\ (\mathrm{chart}\ z)\ s\bigr)\Bigr\| \le \varepsilon.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedBufferedRowDensityProduct_error` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedGlobalMaskedDensity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B144`, `OAIErdos3B149` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedGlobalMaskedDensity.lean#L46

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B172

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

include hR hC hchart hbudget in
theorem allocatedBufferedRowDensityProduct_error {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (D : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ) (ε : ℝ) (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region)
    (herr : ‖((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ) -
        ∑ k, a k * ∏ s, f k s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s)‖ ≤ ε) :
    ‖cutoff (chart z) * (((∏ q : (Σ a : {a // ¬grid a}, rowTypes a.val.1), R q.1.val.1 : ℝ) : ℂ) *
        (D
          (allocatedLongJetRealCoordinates B U b S (split z.1).2) : ℂ)) -
      ∑ k, a k * ∏ s, factor (f k s) (coveredRowsSiteValue rowSets U (chart z) s)‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
