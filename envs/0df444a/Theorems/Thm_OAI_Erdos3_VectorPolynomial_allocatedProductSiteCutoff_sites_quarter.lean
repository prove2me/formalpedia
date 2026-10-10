-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductSiteCutoff_sites_quarter
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_sites_quarter
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:41:09.696988+00:00
-- url     : https://prove2.me/theorems/b12376d2-0435-41b0-bda3-827197046e05
-- title:
--   A nonzero product site cutoff puts every row-restricted site in the quarter-box region
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)` and $W_j = $ `latticeSection (standardEuclideanLattice (J j)) V_j` $= \mathbb Z^{J_j} \cap V_j$; bases $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a layer-sampler scale `S : LayerSamplerScale B U b R σ`; a finite type $\alpha$ with decidable equality and, for each $j$, a finite family $\mathrm{rowSets}_j$ of subsets of $\alpha$, with row types $\mathrm{rowTypes}_j = \{t : t \in \mathrm{rowSets}_j\}$; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; the hypothesis $hb$ that the $\mathbb Z$-span of each $b_j$ is `projectedIntegerLattice V_j`; finite types $E_j$ and $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $E_j$; a positive natural number $d$; $r \in \mathbb R_{\ge 0}$ with $0 < r$; the hypothesis $R_j > 0$ for all $j$; reals $C_j \ge 0$ such that $\|(\texttt{normalizedOrthogonalChart}\ V_j\ b_j)^{-1}(v)\| \le C_j \|v\|$ for all $j, v$ (`normalizedOrthogonalChart` is a continuous linear equivalence $\mathbb R^{J_j} \simeq V_j \times \mathbb R^{n_j}$ defined by OpenAI). Let $\mathrm{pointCap}_j = C_j\,(|I_j| + 1)\,(2 r R_j)$.
--
--   Assume $(|\mathrm{rowSets}_j| + 1)\,\bigl(2^{|\alpha|} \cdot \mathrm{pointCap}_j\bigr) \le 1/4$ for every $j$. Let $z$ be a point of `MixedCoveredJetSource I rowTypes E n d` lying in `mixedCoveredJetRegion U o b d` for the closed quarter boxes $\{x : |x_i| \le 1/4\}$ (`standardLatticeClosedQuarterBox`) at every row, and suppose `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z)` $\ne 0$, where chart is `mixedCoveredJetChart U o b hb bW d` and `allocatedProductSiteCutoff` is the product over $s \subseteq \alpha$ of complex site factors defined by OpenAI. Then for every subset $s \subseteq \alpha$, the single-row source point `mixedCoveredRowsSiteValue rowSets d z s` (an integer-matrix image of $z$ defined by OpenAI) lies in `mixedCoveredJetRegion U o b d` for the closed quarter boxes, with one row per layer.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_sites_quarter` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedProductSiteSupport.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B149` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedProductSiteSupport.lean#L78

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B172

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "siteChart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "siteRegion" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "pointCap" => (fun j => C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))

include hR hC hchart in
theorem allocatedProductSiteCutoff_sites_quarter
    (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) * pointCap j) ≤ 1 / 4)
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hz : z ∈ mixedCoveredJetRegion (E := E) U o b d
      (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j)))
    (hne : allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) ≠ 0)
    (s : Finset α) :
    mixedCoveredRowsSiteValue rowSets d z s ∈ siteRegion := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
