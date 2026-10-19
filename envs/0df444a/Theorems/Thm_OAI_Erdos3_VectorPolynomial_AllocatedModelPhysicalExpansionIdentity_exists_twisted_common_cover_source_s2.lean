-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedModelPhysicalExpansionIdentity_exists_twisted_common_cover_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:59:31.496686+00:00
-- url     : https://prove2.me/theorems/d384aae9-5d97-4555-b618-3b70fca80b6c
-- title:
--   A positive recentered model source yields a large twisted common-cover window sum
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); $\mathrm{dim} \in \mathbb N$, with $\mathrm{rowSets}_j =$ `boundedBooleanJetRows (Fin dim) (j+1)` (the subsets of $\mathrm{Fin}\,\mathrm{dim}$ of size at most $j+1$), and grid the predicate `allocatedGridAxis U b S.value`; finite types $E_j$; a point $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`; $q \in \mathbb N$ and natural numbers $d, \mathrm{period} \ne 0$; $r \in \mathbb R_{>0}$ (hr); $\mathbb Z$-span of $b_j$ equal to `projectedIntegerLattice (euclideanSubspace (U j))` (hb); orthonormal bases $o_j$ of `euclideanSubspace (U j)` indexed by $I_j$; $\mathbb Z$-bases $bW_j$ (indexed by $E_j$) of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))`; a family $e$ of `ScalarSiteExpansion`s on $\mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$ indexed by the grid axes (finite families of terms with periods, complex coefficients and factors $\mathbb Z/p \times \mathbb R \to \mathbb C$); a finite type $T$, $a : T \to \mathbb C$ and $f : T \to \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb R^{\texttt{LayerSamplerAxis I n}} \to \mathbb C$; a finite type $X$ and `VectorPolynomial X ℝ (J j → ℝ)`s $p_j$ with all coefficients in $U_j$ (hm); a natural number $\mathrm{spatialModulus} \ne 0$ and $\mathrm{stride}, N : X \to \mathbb N$, with refined $=$ `residueRefinedPeriod spatialModulus stride` $= \mathrm{spatialModulus}\cdot\prod_x \mathrm{stride}(x)$; a map wholeReference from residue labels ($\mathrm{FullInput} \to \mathrm{Option}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z/\mathrm{refined}$, FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`) to integer tuples in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S)`, and one such label; $M \in \mathbb N$ with $M > 0$ (hM); an embedding $\mathrm{selection} : \mathrm{Fin}\,\mathrm{dim} \hookrightarrow G$ with `GoodScalarKernelTuple selection (1/M) M x` (hx: the normalized scalar-cube minor at selection exceeds $1/M$ in absolute value and the column lattice of `scalarCubeDifferenceMatrix x` contains $a\,\mathbb Z^{\mathrm{Fin}\,\mathrm{dim}}$ for some natural number $0 < a \le M$); reals $W, \tau, \xi, \mathrm{mesh}$ with $W \ge 0$ (hW); $\mathrm{base} : X \to \mathbb Z$; and a finset cells of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride` (residues $\mathbb Z/\mathrm{stride}(x)$ indexed by pairs). Write window $=$ `spatialWindow (trimmedSpatialRootScale τ N stride) 4`, widths $=$ `narrowTrimmedSpatialWidths W τ ξ N`, reconstruct $=$ `allocatedWholeResidueReconstruction B U b S X spatialModulus stride wholeReference x base label`, volume $= \prod_z\prod_i$ `physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i`, terms $= X \to$ `SpatialSiteLabel (Fin dim) spatialModulus 4 mesh`, and twist $=$ `allocatedRecenteredSpatialTwist B U b S X spatialModulus stride wholeReference x N mesh base label` (with $\tau$).
--
--   Let $g$ assign to each label $\ell : \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to (\prod_j (\mathbb Z/\mathrm{period})^{\mathrm{Fin}(n_j)}) \times (\prod_j (\mathbb Z/\mathrm{period})^{E_j})$, $i \in T$, term choice $k$ of $e$ and site $s$ a function $g_{\ell,i,k,s}$ from LongSpace $\times$ GridSpace to $\mathbb C$, where LongSpace $= (\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb R/\mathbb Z) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)$ and GridSpace $= \Sigma_j J_j \to \mathbb R/\mathbb Z$. Assume `AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g` (for every $v : X \to (\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}) \to \mathbb Z$, the product of the chart ideal approximation and the full grid chart model at the physical cube row sample of $v$ equals the sum over $\ell, i, k$ of the masked ideal coefficient times `coverSiteCoefficient e k` times $\prod_s g_{\ell,i,k,s}$ at the masked and grid factor inputs). Assume every $g_{\ell,i,k,s}$ is $L$-Lipschitz and bounded by $1$ in norm, for some $L \in \mathbb R_{\ge 0}$; `(e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)` for all grid axes $a$, with $V_a \le V_{\max}$ for some $V_{\max} \in \mathbb R_{\ge 0}$; $\mathrm{stride}(z) > 0$ for all $z$ and $\mathrm{mesh} > 0$; `allocatedPhysicalRootBudget B U b S (fun _ => 0)` $\le W$; the lattice $\mathrm{spatialModulus}\cdot\mathbb Z^{\mathrm{Unit}\oplus\mathrm{Fin}\,\mathrm{dim}}$ is contained in `pivotFullImage` of the selected spatial pivot and free columns of $(g \mapsto x_g(\mathrm{none}))$ and `scalarCubeDifferenceMatrix x` at selection; widths are positive and $\sum_z$ `selectedResidueSmoothWeight stride cells widths z` $> 0$. Let $\mathrm{test} : \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim}) \to \mathbb R^X \to \mathbb C$ and reals $\delta, C_{\mathrm{model}}, C_{\mathrm{spatial}} > 0$ with $\sum_{\ell, i, k}\|2^{2^{\mathrm{dim}}}\cdot\texttt{allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a ℓ i}\cdot\texttt{coverSiteCoefficient e k}\| \le C_{\mathrm{model}}$, `allocatedSpatialCoefficientCap X selection M spatialModulus mesh` $\le C_{\mathrm{spatial}}$, and $\delta \le \mathrm{Re}$ of `allocatedRecenteredFiniteModelSource B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label hM selection hx hW base cells test` (with $\tau, \xi, \mathrm{mesh}$).
--
--   Then there exist a natural number cover with $0 < \mathrm{cover} \le \mathrm{period}\cdot V_{\max}^{|\mathrm{gridAxes}|}$, and functions $F_s : (\Sigma_j J_j \to \mathbb R/\mathbb Z) \to \mathbb C$ for $s \in \mathrm{Finset}(\mathrm{Fin}\,\mathrm{dim})$, each $L\cdot\mathrm{period}\cdot V_{\max}^{|\mathrm{gridAxes}|}$-Lipschitz and of norm at most $1$, and there exist a cell $c \in$ cells and $t \in$ terms such that `allocatedSpatialExpansionCoefficient B U b S x X hM selection hx spatialModulus hW mesh (principalResidueLabel spatialModulus (wholeReference label)) t` $\ne 0$, $\|\mathrm{twist}(c, t, s, u)\| \le 1$ for all $s, u$, and
--   $$\frac{\delta}{C_{\mathrm{model}}C_{\mathrm{spatial}}} \le \Bigl\|\frac{1}{\mathrm{volume}}\sum_{v \in \mathrm{window}}\Bigl(\prod_s \mathrm{test}(s, \hat v_s)\cdot\mathrm{twist}(c, t, s, \hat v_s)\Bigr)\prod_s F_s\bigl(\texttt{physicalGridFactorInput cover p}\ \hat v_s\bigr)\Bigr\|,$$
--   where $\hat v_s =$ `physicalCubeVertexValue (reconstruct c v) s` (the vertex $u \mapsto w_u(\mathrm{inl}) + \sum_{a \in s} w_u(\mathrm{inr}\,a)$ of the reconstructed cube $w$), read as an integer or real vector as needed, and `physicalGridFactorInput cover p t` is $\langle j, i\rangle \mapsto p_j(t)_i/\mathrm{cover} \bmod 1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedNormalizedNativeModel.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B236` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedNormalizedNativeModel.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} [Fintype X] (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => (X → SpatialSiteLabel (Fin dim) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X spatialModulus stride wholeReference x N mesh base label

theorem AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    {δ Cmodel Cspatial : ℝ} (hδ : 0 < δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmodel)
    (hspatial : allocatedSpatialCoefficientCap X selection M spatialModulus mesh ≤ Cspatial)
    (hpositive : δ ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells test).re) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      allocatedSpatialExpansionCoefficient B U b S x X hM selection hx spatialModulus hW mesh
        (principalResidueLabel spatialModulus (wholeReference label)) t ≠ 0 ∧
      (∀ site u, ‖twist cell.val t site u‖ ≤ 1) ∧
      δ / (Cmodel * Cspatial) ≤ ‖(∑ v ∈ window,
        (∏ site, test site (fun u => (physicalCubeVertexValue (reconstruct cell.val v) site u : ℝ)) *
          twist cell.val t site (physicalCubeVertexValue (reconstruct cell.val v) site)) *
        ∏ site, F site (physicalGridFactorInput cover p
          (fun u => (physicalCubeVertexValue (reconstruct cell.val v) site u : ℝ)))) / ((volume : ℝ) : ℂ)‖ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
