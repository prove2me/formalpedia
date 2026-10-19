-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedBufferedRowIdealProduct_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedBufferedRowIdealProduct_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:57:55.604193+00:00
-- url     : https://prove2.me/theorems/8ce32d17-069a-4cc6-9c42-d36d8ada95d6
-- title:
--   On the covered quarter-box region, the product of buffered site factors equals the product cutoff times the row-ideal values
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j < m$) finite types, $n : \mathrm{Fin}(m) \to \mathbb{N}$, and $B_a$ finite types indexed by `LayerSamplerAxis I n` $= \Sigma_{j<m} (I_j \sqcup \mathrm{Fin}(n_j))$. Let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, $b_j$ bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)` whose $\mathbb{Z}$-span is the projected integer lattice (hypothesis `hb`), $R, \sigma : \mathrm{Fin}(m) \to \mathbb{R}$, `S : LayerSamplerScale B U b R σ` (OpenAI's layer sampler scale data), $o_j$ orthonormal bases of `euclideanSubspace (U j)` indexed by $I_j$, $E_j$ finite types and `bW j` $\mathbb{Z}$-bases (indexed by $E_j$) of the lattice section of $\mathbb{Z}^{J_j}$ in `euclideanSubspace (U j)`. Let $d \ge 1$ be a natural number and $r \in \mathbb{R}_{\ge 0}$ with $r > 0$. Let $\alpha$ be a finite type with decidable equality and `rowSets j` a finite set of finite subsets of $\alpha$ for each $j$; write `rowTypes j` for the subtype of `rowSets j`.
--
--   Assume: $R_j > 0$ for all $j$; $C : \mathrm{Fin}(m) \to \mathbb{R}$ with $C_j \ge 0$; for all $j$ and $v$, $\|\Phi_j^{-1}(v)\| \le C_j \|v\|$ where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` (the linear chart $x \mapsto$ (projection of $x$ onto $U_j$, normalized $b_j$-coordinates of its orthogonal part)); and for all $j$,
--   $$(|\texttt{rowSets}\ j| + 1)\cdot\Bigl(2^{|\alpha|}\cdot\bigl(C_j\,((|I_j| + 1)(2 r R_j))\bigr)\Bigr) \le \tfrac14,$$
--   where $2^{|\alpha|} = |\mathrm{Finset}\ \alpha|$.
--
--   Let $f : \mathrm{Finset}\ \alpha \to (\texttt{LayerSamplerAxis I n} \to \mathbb{R}) \to \mathbb{C}$. Let $z$ be a point of `MixedCoveredJetSource I rowTypes E n d` (OpenAI's type of pairs: for each $j$, a real array $I_j \times \texttt{rowTypes}\ j \to \mathbb{R}$ and an integer array $\mathrm{Fin}(n_j) \times \texttt{rowTypes}\ j \to \mathbb{Z}$, together with residues in $\mathbb{Z}/d\mathbb{Z}$ indexed by $\texttt{rowTypes}\ j \times E_j$) lying in `mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))` (the region whose coordinates lie in the closed box $\{x : |x_i| \le 1/4\ \forall i\}$ in each slot). Let $\mathrm{chart}(z)$ = `mixedCoveredJetChart U o b hb bW d z` $\in$ `EuclideanJetLayers U rowTypes` (a family of points of the tori `euclideanSubspace (U j)` modulo the lattice section). Then
--   $$\prod_{s \in \mathrm{Finset}\ \alpha} \texttt{factor}\bigl(f(s)\bigr)\bigl(\texttt{coveredRowsSiteValue rowSets U}\ (\mathrm{chart}\ z)\ s\bigr) = \texttt{cutoff}(\mathrm{chart}\ z)\cdot \prod_{s \in \mathrm{Finset}\ \alpha} f(s)\bigl(\texttt{allocatedRowIdealCoordinates B U b S rowSets}\ w\ s\bigr),$$
--   where `factor` is `allocatedBufferedSiteChartFactor B U b S o hb bW d r hr` (OpenAI's buffered chart density of a site function), `coveredRowsSiteValue rowSets U y s` is the single-row torus point $j \mapsto \sum_t M^{(j)}_{s,t}\, y_{j,t}$ with OpenAI's row-restricted site matrix $M^{(j)}$, `cutoff` is `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr` (the same product with every $f(s)$ replaced by the constant $1$), and $w$ is the second component of `coefficientJetAxisSplit rowTypes I n (allocatedGridAxis U b S.value)` applied to the first component of $z$ (the coefficient rows on the non-grid axes).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedBufferedRowIdealProduct_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedBufferedRowIdealProduct` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalNormalizer.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCanonicalNormalizer.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedBufferedRowIdealProduct)

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

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
theorem allocatedBufferedRowIdealProduct_s2
    (f : Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (z : MixedCoveredJetSource I rowTypes E n d) (hz : z ∈ region) :
    (∏ s, factor (f s) (coveredRowsSiteValue rowSets U (chart z) s)) =
      cutoff (chart z) * ∏ s, f s (allocatedRowIdealCoordinates B U b S rowSets (split z.1).2 s) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
