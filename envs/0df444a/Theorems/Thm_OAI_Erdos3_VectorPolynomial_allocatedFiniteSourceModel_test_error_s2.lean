-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiniteSourceModel_test_error_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFiniteSourceModel_test_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:38:42.117987+00:00
-- url     : https://prove2.me/theorems/ba1b3127-dc3f-4803-be55-ce53d42e8e8d
-- title:
--   A source uniformly close to the finite model has test integrals within the same error
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality and finite families $\mathrm{rowSets}_j$ of finsets of $\alpha$ (rowTypes$_j$ is the subtype of $\mathrm{rowSets}_j$); grid the predicate `allocatedGridAxis U b S.value`; finite types $E_j$; a point $x : G \to$ `IntegerScalarCubeBox α S.value`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`; $q \in \mathbb N$ and natural numbers $d, \mathrm{period} \ne 0$; $r \in \mathbb R_{>0}$ (hr); $\mathbb Z$-span of $b_j$ equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; and $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`.
--
--   Let $\mu$ be a probability measure on `EuclideanJetLayers U rowTypes` (for each $j$ and row, a point of the torus `euclideanSubspace (U j)` modulo the lattice section). Let $K$ be a finite type, $a : K \to \mathbb C$, and $f : K \to \mathrm{Finset}\,\alpha \to \mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C$ with every $f(k, s)$ $L$-Lipschitz for some $L \in \mathbb R_{\ge 0}$ and $\|f(k,s)(v)\| \le 1$. Let $e$ be a family of `ScalarSiteExpansion`s on $\mathrm{Finset}\,\alpha$ indexed by the grid axes, with `(e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)` for all $a$, for some real functions $N_t, V, C_c, H_s$ on the grid axes and $L_g \in \mathbb R_{\ge 0}$. Let source be a measurable complex function on `EuclideanJetLayers U rowTypes` and $\varepsilon$ a real with
--   $$\|\mathrm{source}(y) - \mathcal A(y)\,\mathcal G(y)\| \le \varepsilon \quad\text{for all } y,$$
--   where $\mathcal A =$ `allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f` and $\mathcal G =$ `allocatedFullGridChartModel B U b S rowSets d hb o bW e`. Let $\varphi$ be a measurable complex function on the same space with $\|\varphi(y)\| \le 1$ for all $y$. Then source is $\mu$-integrable and
--   $$\Bigl\|\int \mathrm{source}(y)\,\varphi(y)\,d\mu(y) - \int \mathcal A(y)\,\mathcal G(y)\,\varphi(y)\,d\mu(y)\Bigr\| \le \varepsilon.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFiniteSourceModel_test_error_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFiniteSourceModel_test_error` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedFiniteModelComparison.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedFiniteModelComparison.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFiniteSourceModel_test_error)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section

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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

theorem allocatedFiniteSourceModel_test_error_s2
    (μ : Measure (EuclideanJetLayers U rowTypes)) [IsProbabilityMeasure μ]
    {K : Type*} [Fintype K]
    (a : K → ℂ) (f : K → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    {L : ℝ≥0} (hLf : ∀ k s, LipschitzWith L (f k s)) (hf : ∀ k s v, ‖f k s v‖ ≤ 1)
    (e : {a // grid a} → ScalarSiteExpansion (Finset α))
    {Nt V Cc Hs : {a // grid a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (source : EuclideanJetLayers U rowTypes → ℂ) (hsource : Measurable source)
    {ε : ℝ}
    (herr : ∀ y, ‖source y -
      allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
        allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤ ε)
    (φ : EuclideanJetLayers U rowTypes → ℂ) (hφ : Measurable φ) (hφb : ∀ y, ‖φ y‖ ≤ 1) :
    Integrable source μ ∧
      ‖(∫ y, source y * φ y ∂μ) - ∫ y,
        (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
          allocatedFullGridChartModel B U b S rowSets d hb o bW e y) * φ y ∂μ‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
