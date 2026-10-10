-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecenteredSelectedMean_l1_source
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRecenteredSelectedMean_l1_source
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T09:49:26.197814+00:00
-- url     : https://prove2.me/theorems/07bcece5-f366-440e-8805-e64eb3118c0a
-- title:
--   A large recentered profile mean transfers to the recentered model source up to δ
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$, with fullTuple $=$ `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`; a finite type $X$, a natural number $\mathrm{modulus} \ne 0$ and $q : X \to \mathbb N$, with refined $=$ `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_t q(t)$ and labels the maps $\mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$ (FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`); a map wholeReference from labels to fullTuple; a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; $M \in \mathbb N$ with $M > 0$ (hM); an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x` (hx); $N : X \to \mathbb N$; reals $W, \tau, \xi$ with $W \ge 0$ (hW); a real mesh; $\mathrm{base} : X \to \mathbb Z$; a finset cells of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q`; types $O_j$; a map point from integer cubes $X \to (\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$ to `EuclideanJetLayers U O` (for each $j$ and $o \in O_j$ a point of `euclideanSubspace (U j)` modulo the lattice section); and test from integer cubes to $\mathbb C$. Let window $=$ `spatialWindow (trimmedSpatialRootScale τ N q) 4`.
--
--   Let law be finite probability weights on fullTuple and $r$ a label such that every $y$ of nonzero weight has `principalResidueLabel refined y` $= r$, and `principalResidueLabel refined (wholeReference r)` $= r$. Let profile $:$ fullTuple $\to$ `EuclideanJetLayers U O` $\to \mathbb C$ and ideal, model $:$ `EuclideanJetLayers U O` $\to \mathbb C$. Assume $q(t) > 0$, $N(t) > 0$, $\tau > 0$, `allocatedPhysicalRootBudget B U b S (fun _ => 0)` $\le W$, $\mathrm{mesh} > 0$, the lattice $\mathrm{modulus}\cdot\mathbb Z^{\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}}$ is contained in `pivotFullImage` of the selected spatial pivot and free columns of $(g \mapsto x_g(\mathrm{none}))$ and `scalarCubeDifferenceMatrix x` at selection, and $\|\mathrm{test}(w)\| \le 1$ for all $w$. Let $\kappa, \delta, E_{\mathrm{error}}, \varepsilon$ be reals with $\kappa \le \mathrm{Re}$ of the law-mean of `allocatedRecenteredProfileTerm B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile` (with $\tau, \xi$), $\varepsilon \ge 0$, and $\|\mathrm{ideal}(z) - \mathrm{model}(z)\| \le \varepsilon$ for all $z$.
--
--   Put root $=$ `allocatedPhysicalCubeRoot B U b S 0 x (wholeReference r)`, $D =$ `allocatedPhysicalCubeDirections B U b S x (wholeReference r)`, $H =$ `trimmedSpatialRootScale τ N q`, $V =$ `narrowTrimmedSpatialWidths W τ ξ N`, $V_1 =$ `referenceJetEnvelopeWidths q H`, $C = (\mathrm{modulus}^{\mathrm{dim}+1}\cdot$`anisotropicSpatialDensityCap selection (1/M)`$)^{|X|}$, and $\mathrm{volumeFactor} = (30/\texttt{smoothProbabilityProfile 0})^{(\mathrm{dim}+1)|X|}\cdot((1+W)/S.\mathrm{value})^{\mathrm{dim}\cdot|X|}$. Then: if $V > 0$ everywhere; $\sum_z$ `selectedResidueSmoothWeight q cells V z` $> 0$; $\sum_k |\texttt{physicalCubeCoefficient root D i k}| \le H(t)$ for all $t, i$; $8\cdot$`probabilityProfileLipschitz` $\le 20H(t)$ and $1 \le H(t)$ for all $t$; for every cell $a$, with target the column residue pattern mod $q$ of `standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative q a))`, both $\sum_z$ `selectedResidueSmoothWeight q {target} V₁ z` $> 0$ and `selectedResidueDensityMass q {target} V₁` of $z \mapsto \|\mathrm{law.mean}(y \mapsto \mathrm{profile}(y, \mathrm{point}(w_z))) - \mathrm{ideal}(\mathrm{point}(w_z))\|$ is at most $E_{\mathrm{error}}$, where $w_z =$ `translatePhysicalCube base (standardPhysicalCubeOutput z)`; and $C\bigl(\mathrm{volumeFactor}\cdot E_{\mathrm{error}} + 9^{(\mathrm{dim}+1)|X|}((1+W)/S.\mathrm{value})^{\mathrm{dim}\cdot|X|}\varepsilon\bigr) \le \delta$; then
--   $$\kappa - \delta \le \mathrm{Re}\sum_{(c, v) \in \mathrm{cells}\times\mathrm{window}}\texttt{selectedResidueCellWeight q cells V c}\cdot\texttt{allocatedRecenteredResidueWeight B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells test r c v}\cdot\mathrm{model}\bigl(\mathrm{point}(\texttt{allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r c v})\bigr)$$
--   (the residue weight taken with $\tau$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRecenteredSelectedMean_l1_source` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedRecenteredL1Source.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B162`, `OAIErdos3B200` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedRecenteredL1Source.lean#L557

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B200

namespace OAI

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
local notation "target" a => columnResiduePattern stride
  (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative stride a)))
local notation "V₁" => referenceJetEnvelopeWidths (q := dim) stride H

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

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

theorem allocatedRecenteredSelectedMean_l1_source
    (law : FiniteProbabilityWeights fullTuple) (r : labels)
    (hlabel : ∀ y, law.weight y ≠ 0 → principalResidueLabel refined y = r)
    (hwhole : principalResidueLabel refined (wholeReference r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    (ideal model : EuclideanJetLayers U O → ℂ)
    (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (htest : ∀ w, ‖test w‖ ≤ 1) {κ δ Eerror ε : ℝ}
    (hsource : κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile)).re)
    (hε : 0 ≤ ε) (htrunc : ∀ z, ‖ideal z - model z‖ ≤ ε) :
    let root := allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r)
    let D := allocatedPhysicalCubeDirections B U b S x (wholeReference r)
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let V₁ := referenceJetEnvelopeWidths (q := dim) q H
    let _A := (∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i : ℝ)
    let C := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X
    (∀ z, 0 < V z) → (0 < ∑' z, selectedResidueSmoothWeight q cells V z) →
    (∀ t i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    (∀ t, 1 ≤ H t) →
    (∀ a : cells,
      let target := columnResiduePattern q (standardPhysicalCubeFrame
        (physicalCubeRootDifferences root D 0 (boundedColumnResidueRepresentative q a.val)))
      (0 < ∑' z, selectedResidueSmoothWeight q {target} V₁ z) ∧
      selectedResidueDensityMass q {target} V₁ (fun z =>
        ‖law.complexMean (fun y => profile y (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          ideal (point (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ Eerror) →
    C * (volumeFactor * Eerror + ((9 : ℝ) ^ Fintype.card (X × (Unit ⊕ Fin dim)) *
      (((1 + W) / S.value) ^ dim) ^ Fintype.card X) * ε) ≤ δ →
    κ - δ ≤
      (∑ t : cells × window, (selectedResidueCellWeight q cells V t.1 : ℂ) *
        allocatedRecenteredResidueWeight (τ := τ) B U b S X modulus q wholeReference x hM selection hx
          N hW mesh base cells test r t.1 t.2.val *
        model (point (allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base r
          t.1.val t.2.val))).re := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
