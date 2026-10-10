-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedMaskedSiteChartFactor_measurable
-- name    : OAI.Erdos3.VectorPolynomial.allocatedMaskedSiteChartFactor_measurable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T02:05:32.646799+00:00
-- url     : https://prove2.me/theorems/dd8be4a9-d11c-4bbd-a24a-b8f4654133ea
-- title:
--   The allocated masked site chart factor is measurable
-- statement:
--   Fix the section data: a natural number $m$; finite types $G$ and $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \sqcup \mathrm{Fin}\,n_j$); finite types $J_j$ with real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)` and $W_j = $ `latticeSection (standardEuclideanLattice (J j)) V_j` $= \mathbb Z^{J_j} \cap V_j$; bases $b_j$ of $V_j^\perp$ indexed by $\mathrm{Fin}\,n_j$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a layer-sampler scale `S : LayerSamplerScale B U b R σ`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; the hypothesis $hb$ that the $\mathbb Z$-span of each $b_j$ is `projectedIntegerLattice V_j` (the orthogonal projection of $\mathbb Z^{J_j}$ onto $V_j^\perp$); finite types $E_j$ and $\mathbb Z$-bases $bW_j$ of $W_j$ indexed by $E_j$; a positive natural number $d$; $r \in \mathbb R_{\ge 0}$ with $0 < r$; and a positive natural number $\mathrm{period}$. Let $\mathrm{label} \in \bigl(\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}\bigr) \times \bigl(\prod_j E_j \to \mathbb Z/\mathrm{period}\bigr)$ and let $f : (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$ be $L$-Lipschitz for some $L \in \mathbb R_{\ge 0}$ with $\|f(v)\| \le 1$ for all $v$. Then the function `allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f` from `EuclideanJetLayers U (fun _ => Unit)` $= \prod_j V_j/W_j$ to $\mathbb C$ is measurable. By definition this function is `restrictedComplexChartDensity chart region 1 g`, where chart is `mixedCoveredJetChart` and region is `mixedCoveredJetRegion` for the closed quarter boxes $\{x : |x_i| \le 1/4\}$, both with one row per layer, and $g(w)$ is `allocatedBufferedMixedSiteFactor B U b S r hr f` evaluated at the regrouped real and integer arrays of $w$ when `mixedCoveredSiteResidue d period w` $= \mathrm{label}$, and $0$ otherwise.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedMaskedSiteChartFactor_measurable` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedMaskedChartProduct.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B150` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedMaskedChartProduct.lean#L95

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B150

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
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
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d quarter

theorem allocatedMaskedSiteChartFactor_measurable [NeZero period]
    (label : (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))
    (f : (LayerSamplerAxis I n → ℝ) → ℂ) {L : ℝ≥0}
    (hf : LipschitzWith L f) (hf1 : ∀ v, ‖f v‖ ≤ 1) :
    Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label f) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
