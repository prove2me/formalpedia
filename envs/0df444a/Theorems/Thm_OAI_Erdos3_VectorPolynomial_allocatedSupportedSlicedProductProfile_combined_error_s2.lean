-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedProductProfile_combined_error_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:08.200535+00:00
-- url     : https://prove2.me/theorems/7132eadd-efb4-480a-8d91-d3705b0b6773
-- title:
--   Combined error bound for the site cutoff times the grid-law covered profile against the full-grid chart model
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type with decidable equality to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ inside $\mathbb{R}^{J_j}$), $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (OpenAI's structure with a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality and $\mathrm{rowSets}_j$ a finite set of subsets of $\alpha$ for each $j$; write $O_j$ for the type of members of $\mathrm{rowSets}_j$ and $\mathrm{rows}_j$ for the inclusion $O_j \to \operatorname{Finset} \alpha$. Write `grid` for OpenAI's predicate `allocatedGridAxis U b S.value` on axes. (All named objects are defined by OpenAI.)
--
--   Let $H, \mathrm{step}$ (natural numbers) and $c$ (integers) be functions on the triples `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H > 0$ and each progression $\{c(t) + \mathrm{step}(t)\, i : 0 \le i < H(t)\}$ contained in $[0, \texttt{allocatedPrincipalSides B U b S t})$. Let $q$ be a natural number and $r$ assign to each triple and each element of $\operatorname{Option} \alpha$ a residue in $\mathbb{Z}/q$, such that the `principalTupleWeights B (layerSamplerDegree I n) H hH` mass of the tuples $y$ with `principalResidueLabel q y` $= r$ is positive (hcell); let `gridLaw` be `containedSupportedProgressionAxisLaw` of these data restricted to the grid axes. Let $x : G \to$ `IntegerScalarCubeBox α S.value`, let $u_0$ be a principal axis tuple on the grid axes with nonzero `gridLaw` weight (hu₀), let $v_0$ be a principal axis tuple on the non-grid axes, and let $y_0$ = `principalAxisJoin grid u₀ v₀`. Let $Q_j$ be finite types and $d$ a positive natural number. Assume (hperiod) for every $j$ the lattice $q \cdot \mathbb{Z}^{O_j}$ is contained in the image of `scalarKernelIntegerJet x (j+1) rows_j`. Assume the integer span of $b_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))` (hb), let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, and $bW_j$ a $\mathbb{Z}$-basis indexed by $Q_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`.
--
--   Let $f$ be a real function of real vectors indexed by pairs (non-grid axis $a = (j, \cdot)$, element of $O_j$). Assume the `principalTupleWeights B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) _` mass of the tuples $y$ with `principalResidueLabel q y` $=$ `principalResidueLabel q y₀` is positive (hfullcell). Let $\mathrm{rad} > 0$ be a nonnegative real, and $e$ assign to each grid axis a `ScalarSiteExpansion (Finset α)` (OpenAI's structure: a finite set of terms with periods, complex coefficients, and factor functions). Let $\varepsilon, \eta$ be reals with
--   $$\bigl\| \texttt{allocatedFullGridNaturalVolume B U b S rowSets} \cdot \mathrm{gridDensity}(z) - \texttt{allocatedFullGridSiteApproximation B U b S rowSets e}\ z \bigr\| \le \varepsilon$$
--   for every $z \in$ `AllocatedFrozenJetRows B U b S O`, where $\mathrm{gridDensity}$ = `allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x`. Let $N_t, V, C_c, H_s$ be real functions on the grid axes and $L \ge 0$ with `(e a).Bounds (Nt a) (V a) (Cc a) L (Hs a)` for every grid axis $a$ (at most $N_t(a)$ terms, periods positive and at most $V(a)$, coefficient $\ell^1$ norm at most $C_c(a)$, factors bounded by $1$, $L$-Lipschitz and vanishing when $|x| \ge H_s(a)$). Let $F$ be a complex function on `EuclideanJetLayers U O` with $\eta \ge 0$ and $\|\Pi(y') - F(y')\| \le \eta$ for all $y'$, where $\Pi$ = `allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f`. Then for every $y \in$ `EuclideanJetLayers U O`,
--   $$\Bigl\| \texttt{allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad}\ y \cdot \mathbb{E}_{u \sim \texttt{gridLaw}}\, \texttt{allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (principalAxisJoin grid u v₀) q f}\ y - F(y) \cdot \texttt{allocatedFullGridChartModel B U b S rowSets d hb o bW e}\ y \Bigr\| \le \|\Pi(y)\|\, \varepsilon + \eta \prod_{a} C_c(a),$$
--   the product running over the grid axes and the real mean being cast to $\mathbb{C}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedUniformPhysicalSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedProductProfile_combined_error)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid

variable (x : G → IntegerScalarCubeBox α S.value)
variable (u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]
variable (hperiod : ∀ j, integerScalarLattice ((fun j : Fin m => {t : Finset α // t ∈ rowSets j}) j) (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) ((fun j => (Subtype.val : rowSets j → Finset α)) j)).mulVecLin.range)

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "y₀" => principalAxisJoin grid u₀ v₀
local notation "gridDensity" => allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x

include hu₀ hperiod in

theorem allocatedSupportedSlicedProductProfile_combined_error_s2
    (f : ((Σ a : {a // ¬grid a}, rowTypes a.val.1) → ℝ) → ℝ)
    (hfullcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (rad : ℝ≥0) (hrad : 0 < rad)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε η : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S rowTypes,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) * (gridDensity z : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε)
    {Nt V Cc Hs : gridAxes → ℝ} {L : ℝ≥0}
    (heb : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) L (Hs a))
    (F : EuclideanJetLayers U rowTypes → ℂ) (hη : 0 ≤ η)
    (hF : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y - F y‖ ≤ η)
    (y : EuclideanJetLayers U rowTypes) :
    ‖allocatedProductSiteCutoff B U b S rowSets o hb bW d rad hrad y *
      ((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
        (principalAxisJoin grid u v₀) q f y) : ℂ) -
      F y * allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
    ‖allocatedProductFullGridPrefactor B U b S rowSets d rad hrad x hb o bW q y₀ f y‖ * ε + η * ∏ a, Cc a := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
