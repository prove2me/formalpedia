-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrowTrimmed_early_coarse_source_law
-- name    : OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_early_coarse_source_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T19:09:15.361239+00:00
-- url     : https://prove2.me/theorems/b9588d00-97bd-425a-994a-247a3c79f3f9
-- title:
--   A projected source-law lower bound transfers to the term at the early recentered mesh
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$) with decidable equality, $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ with decidable equality indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities), and $\mathrm{dim} \in \mathbb N$. Write $\mathcal T$ for `PrincipalTupleIndex B (layerSamplerDegree I n)`, $\mathcal V$ for `LayerSamplerVariables G I n B`, and fullTuple for `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`. Let $X$ be a finite type, $\mathrm{modulus} \ne 0$ a natural number, $q : X \to \mathbb N$ with $q > 0$ pointwise, $\mathrm{refined} =$ `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_t q(t)$, and wholeReference a map from labels $\mathcal T \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$ to fullTuple. Let $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value` (integer vectors indexed by $\mathrm{Option}(\mathrm{Fin}\,\mathrm{dim})$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $M > 0$ a natural number, $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x`, $N : X \to \mathbb N$ with $N > 0$ pointwise, reals $W \ge 0$, $\tau > 0$, $\xi$ with $0 < \xi \le 1$, a real $\mathrm{mesh} > 0$, $\mathrm{base} : X \to \mathbb Z$, a finite set cells of `ColumnResiduePattern (Option 𝒱) X q`, types $O_j$, maps point from $X \to (\mathrm{Unit} \oplus \mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$ to `EuclideanJetLayers U O` and test from the same domain to $\mathbb C$ with $\|\mathrm{test}(v)\| \le 1$ for all $v$, and reals $C_0, \rho, \delta$. Write $V$ for `narrowTrimmedSpatialWidths W τ ξ N` (positive by OpenAI's lemma `narrowTrimmedSpatialWidths_pos`), $E_{\mathrm{entry}}$ for `allocatedPhysicalEntryBudget B U b S 0`, and $\lambda$ for the constant `probabilityProfileLipschitz`. Assume: $0 < \rho$; `allocatedPhysicalRootBudget B U b S 0` $\le W$; $1 \le C_0$, $S.\mathrm{value} \le C_0$, $W \le C_0$; $8(1+W)\,q(t)\,\rho \le \xi\tau N(t)$ for all $t$; `anisotropicSpatialMeshThreshold selection 𝒯 C₀` $\le \rho$; $8\lambda \le \rho$; the lattice `integerScalarLattice (Unit ⊕ Fin dim) modulus` (multiples of modulus) is contained in `pivotFullImage` of `selectedSpatialPivot r D selection` and `selectedSpatialFreeColumns r D selection`, where $r(g) = 0 + x_g(\mathrm{none})$ and $D =$ `scalarCubeDifferenceMatrix x` (the sum of the ranges of the two integer matrices); $0 \le \delta$; $2\,|\mathrm{Option}\,\mathcal V|\,(2E_{\mathrm{entry}}) \le \rho$; $|\mathcal T|\,(2E_{\mathrm{entry}}) \le \delta\rho$; and $0 < \sum'_z$ `selectedResidueSmoothWeight q cells V z` ($h_{\mathrm{mass}}$). Now let law be `FiniteProbabilityWeights` (a probability vector $w$) on fullTuple such that every $y$ with $w(y) \ne 0$ satisfies `principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y`; let $\mathrm{profile} : \mathrm{fullTuple} \to$ `EuclideanJetLayers U O` $\to \mathbb C$; let $C_g \ge 0$ and $Z \ge 1/2$ be reals with $\|\mathrm{profile}(y)(\mathrm{point}(v))\| \le C_g$ whenever $w(y) \ne 0$; let target and $\kappa$ be reals; assume $\sum_y w(y)\,$`allocatedRecenteredProfileMass B U b S X modulus q wholeReference x N base cells point profile y` (with $W, \tau, \xi$) $\le$ `coarseReferenceMassConstant dim X W S.value` $=: K$, $C_g \cdot 24\lambda\,|\mathrm{Option}\,\mathcal V \times X|/\rho \le \varsigma/2$, and $\mathcal E \cdot K \le \varsigma/2$, where $\varsigma =$ `normalizedSpatialShare target` $= e^{-(\mathrm{target}+2)}$ and $\mathcal E =$ `allocatedTupleSpatialError |X| selection 𝒯 M modulus C₀ ρ ξ W δ mesh`. Let $p, E$ be reals with $p, E \ge 0$, $|G| \le p$, $|X| \le p$, $\mathrm{dim}+1 \le p$, $M \le \exp p$, $\mathrm{modulus} \le M^{m+1}$, $|\mathcal V| \le \exp p$, $W \le |\mathcal V|\,S.\mathrm{value}$, and $\mathrm{mesh} \le \mu_E$, where $\mu_E =$ `allocatedEarlyRecenteredMesh X selection M modulus p E` (a real number). For $y \in \mathrm{fullTuple}$ and $z : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$ let $\Delta_y(z) =$ `physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S 0 x y) (allocatedPhysicalCubeDirections B U b S x y) base z`, and let $\mathrm{projected}(y) = \sum'_z \pi(z)\,\mathrm{test}(\Delta_y(z))\,\mathrm{profile}(y)(\mathrm{point}(\Delta_y(z)))$, where $\pi$ is the probability mass function `selectedResidueSmoothPMF q cells V _ hmass` (taken as real numbers). Then if $\kappa \le \mathrm{Re}\bigl(\sum_y w(y)\,\mathrm{projected}(y) / Z\bigr)$, it follows that
--   $$Z\,(\kappa - e^{-\mathrm{target}}) - e^{-E} \le \mathrm{Re}\Bigl(\textstyle\sum_y w(y)\,\texttt{allocatedRecenteredProfileTerm}\ B\ U\ b\ S\ X\ \mathrm{modulus}\ q\ \mathrm{wholeReference}\ x\ h_M\ \mathrm{selection}\ h_x\ N\ h_W\ \mu_E\ \mathrm{base}\ \mathrm{cells}\ \mathrm{point}\ \mathrm{test}\ \mathrm{profile}\ y\Bigr)$$
--   (with $\tau, \xi$); note that the term on the right uses the mesh $\mu_E$, while the error $\mathcal E$ in the hypotheses uses mesh.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_early_coarse_source_law` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedSpatialToCoarse.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B159` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedSpatialToCoarse.lean#L361

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B159

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable {C₀ ρ δ : ℝ} (hρ : 0 < ρ)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
variable (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
variable (hsize : ∀ t, 8 * (1 + W) * (q t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
variable (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
variable (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hδ : 0 ≤ δ)
variable (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
variable (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ * ρ)
variable (hmeshpos : 0 < mesh)
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "spatialError" => allocatedTupleSpatialError (Fintype.card X) selection
  (PrincipalTupleIndex B (layerSamplerDegree I n)) M modulus C₀ ρ ξ W δ mesh
local notation "boundaryError" => (24 * (probabilityProfileLipschitz : ℝ) *
  Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ)

include hN hq hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hsize hmesh hρ8 hperiod hδ hρshift hρmove hmeshpos htest in
theorem allocatedNarrowTrimmed_early_coarse_source_law
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 1 / 2 ≤ Z) {target κ : ℝ}
    (hmassBound : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value)
    (hboundary : Cg * boundaryError ≤ normalizedSpatialShare target / 2)
    (hsite : spatialError * coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmodulus : modulus ≤ M ^ (m + 1))
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hmeshCoarse : mesh ≤ allocatedEarlyRecenteredMesh X selection M modulus p E) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    κ ≤ (law.complexMean projected / (Z : ℂ)).re →
    Z * (κ - Real.exp (-target)) - Real.exp (-E) ≤
      (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW
          (allocatedEarlyRecenteredMesh X selection M modulus p E) base cells point test profile)).re := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
