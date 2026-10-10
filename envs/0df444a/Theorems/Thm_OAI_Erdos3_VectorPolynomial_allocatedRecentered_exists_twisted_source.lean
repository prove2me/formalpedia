-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecentered_exists_twisted_source
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRecentered_exists_twisted_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T02:30:29.242261+00:00
-- url     : https://prove2.me/theorems/0229eeb9-1d3f-4088-b5da-8ae4e3b506d3
-- title:
--   A large recentered residue-weighted sum yields one large twisted window sum
-- statement:
--   Fix $m, \mathrm{dim} \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Write $\mathcal T$ for `PrincipalTupleIndex B (layerSamplerDegree I n)` and $\mathcal V$ for `LayerSamplerVariables G I n B`. Let $X$ be a finite type, $\mathrm{modulus} \ne 0$ a natural number, $q : X \to \mathbb N$, $\mathrm{refined} =$ `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_z q(z)$, labels the type of maps $\mathcal T \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$, and wholeReference a map from labels to `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`. Let $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value` (integer vectors indexed by $\mathrm{Option}(\mathrm{Fin}\,\mathrm{dim})$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $N : X \to \mathbb N$, reals $\tau$ and mesh, $\mathrm{base} : X \to \mathbb Z$, $M > 0$ a natural number, $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x`, reals $W \ge 0$ and $\xi$, and a finite set cells of `ColumnResiduePattern (Option 𝒱) X q`. Write terms for the type $X \to$ `SpatialSiteLabel (Fin dim) modulus 4 mesh`, $V$ for `narrowTrimmedSpatialWidths W τ ξ N`, window for the finite set `spatialWindow (trimmedSpatialRootScale τ N q) 4` of maps $X \to (\mathrm{Unit} \oplus \mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$, $\mathrm{vol} = \prod_z \prod_i$ `physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i`, $\mathrm{coeff} =$ `allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh`, $\mathrm{rec} =$ `allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base`, and $\mathrm{twist} =$ `allocatedRecenteredSpatialTwist B U b S X modulus q wholeReference x N mesh base` (with $\tau$). Assume $q(z) > 0$ for all $z$, $\mathrm{mesh} > 0$, `allocatedPhysicalRootBudget B U b S 0` $\le W$, that `integerScalarLattice (Unit ⊕ Fin dim) modulus` (the multiples of modulus) is contained in `pivotFullImage (selectedSpatialPivot ker D selection) (selectedSpatialFreeColumns ker D selection)` with $\mathrm{ker}(g) = 0 + x_g(\mathrm{none})$ and $D =$ `scalarCubeDifferenceMatrix x`, that $V(z) > 0$ for all $z$, and that $0 < \sum'_z$ `selectedResidueSmoothWeight q cells V z`. Let $r \in$ labels, $\mathrm{test} : \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb R^X \to \mathbb C$, $F : (X \to (\mathrm{Unit} \oplus \mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z) \to \mathbb C$, and reals $\delta > 0$, $C > 0$ with `allocatedSpatialCoefficientCap X selection M modulus mesh` $\le C$ and
--   $$\delta \le \Bigl\|\textstyle\sum_{a \in \mathrm{cells}} \texttt{selectedResidueCellWeight}\ q\ \mathrm{cells}\ V\ a \cdot \sum_{v \in \mathrm{window}} \texttt{allocatedRecenteredResidueWeight}(\ldots)\ r\ a\ v \cdot F(\mathrm{rec}\ r\ a\ v)\Bigr\|,$$
--   where the weight is `allocatedRecenteredResidueWeight B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells (physicalCubeSiteTest test)` (with $\tau$). Then there exist $a \in \mathrm{cells}$ and $t \in$ terms such that `coeff (principalResidueLabel modulus (wholeReference r)) t` $\ne 0$, $\|\mathrm{twist}\ r\ a\ t\ s\ u\| \le 1$ for all $s, u$, and
--   $$\delta / C \le \Bigl\|\Bigl(\textstyle\sum_{v \in \mathrm{window}} \bigl(\prod_s \mathrm{test}(s)(\pi_s(v)) \cdot \mathrm{twist}\ r\ a\ t\ s\ (\pi_s(v))\bigr)\, F(\mathrm{rec}\ r\ a\ v)\Bigr) / \mathrm{vol}\Bigr\|,$$
--   where $\pi_s(v) =$ `physicalCubeVertexValue (rec r a v) s` $= \bigl(z \mapsto w_z(\mathrm{inl}()) + \sum_{i \in s} w_z(\mathrm{inr}\,i)\bigr)$ for $w = \mathrm{rec}\ r\ a\ v$ (cast to reals where test is applied), the product is over $s \in \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$, and vol is cast to $\mathbb C$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRecentered_exists_twisted_source` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedAmbientBoxTests.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B162`, `OAIErdos3B164` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedAmbientBoxTests.lean#L383

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B164

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W : ℝ} (hW : 0 ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable  (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable (δ : ℝ≥0) (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (hm : ∀ j e, coefficients (p j) e ∈ U j)
variable  (a : cells)

local notation "refined" => residueRefinedPeriod modulus q
local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) [NeZero modulus] (q : X → ℕ)

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (N : X → ℕ) {τ : ℝ} (mesh : ℝ) (base : X → ℤ)

local notation "terms" => (X → SpatialSiteLabel (Fin dim) modulus 4 mesh)

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W ξ : ℝ} (hW : 0 ≤ W)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))

local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N q z) (trimmedSpatialSlopeScale W τ N q z) S.value i
local notation "coeff" => allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X modulus q wholeReference x N mesh base
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4
local notation "V" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

theorem allocatedRecentered_exists_twisted_source
    (hq : ∀ z, 0 < q z) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < V z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight q cells V z)
    (r : labels) (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (F : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hcoeff : allocatedSpatialCoefficientCap X selection M modulus mesh ≤ C)
    (hsource : δ ≤ ‖∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
      ∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) r a v * F (reconstruct r a.val v)‖) :
    ∃ (a : cells) (t : terms),
      coeff (principalResidueLabel modulus (wholeReference r)) t ≠ 0 ∧
      (∀ s u, ‖twist r a.val t s u‖ ≤ 1) ∧
      δ / C ≤ ‖(∑ v ∈ window,
        (∏ s, test s (fun z => (physicalCubeVertexValue (reconstruct r a.val v) s z : ℝ)) *
          twist r a.val t s (physicalCubeVertexValue (reconstruct r a.val v) s)) *
            F (reconstruct r a.val v)) / ((volume : ℝ) : ℂ)‖ := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
