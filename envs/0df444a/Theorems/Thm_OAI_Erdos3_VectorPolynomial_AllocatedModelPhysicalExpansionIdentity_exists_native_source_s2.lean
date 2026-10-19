-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedModelPhysicalExpansionIdentity_exists_native_source_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T07:11:19.329314+00:00
-- url     : https://prove2.me/theorems/286cd5d7-2ece-42b9-9964-29aab2c13ae3
-- title:
--   A physical expansion identity and a positive model source yield a native correlation
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n` ($= \Sigma_j\,(I_j \oplus \mathrm{Fin}\,n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$, $V_j = $ `euclideanSubspace (U j)`, bases $b_j$ (indexed by $\mathrm{Fin}\,n_j$) of $V_j^\perp$; real functions $R, \sigma$ on $\mathrm{Fin}\,m$; a layer-sampler scale `S : LayerSamplerScale B U b R σ` with value $L_S = $ `S.value`; natural numbers $s$ and $n_X$, with row sets $\mathrm{rowSets}_j = $ `boundedBooleanJetRows (Fin (s+1)) (j+1)` and $\mathrm{rows}_j$ their inclusions; finite types $E_j$; a point $x : G \to $ `IntegerScalarCubeBox (Fin (s+1)) L_S`; a tuple $y_0$ in `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s+1)) (allocatedPrincipalSides B U b S)`; natural numbers $q$, $d \neq 0$, $\mathrm{period} \neq 0$; $r \in \mathbb R_{\ge 0}$ with $r > 0$; $hb$: the $\mathbb Z$-span of $b_j$ is `projectedIntegerLattice V_j`; orthonormal bases $o_j$ of $V_j$ indexed by $I_j$; $\mathbb Z$-bases $bW_j$ of $\mathbb Z^{J_j} \cap V_j$ indexed by $E_j$; $e$ assigning to each grid axis (an axis satisfying `allocatedGridAxis U b L_S`) a `ScalarSiteExpansion (Finset (Fin (s+1)))`; a finite type $T$, $a : T \to \mathbb C$ and $f : T \to \mathcal P(\mathrm{Fin}(s+1)) \to (\texttt{LayerSamplerAxis I n} \to \mathbb R) \to \mathbb C$; vector polynomials $p_j \in$ `VectorPolynomial (Fin nX) ℝ (J j → ℝ)` with all coefficients in $U_j$ ($hm$); a natural number $\mathrm{spatialModulus} \neq 0$ and $\mathrm{stride}, N : \mathrm{Fin}\,n_X \to \mathbb N$ with every $N_i \neq 0$, and $\mathrm{refined} = $ `residueRefinedPeriod spatialModulus stride`; a map wholeReference from labels (tuple index $\to \mathrm{Option}(\mathrm{Fin}(s+1)) \to \mathbb Z/\mathrm{refined}$) to full tuples, and one such label $\ell$; a natural number $M > 0$, an embedding $\mathrm{selection} : \mathrm{Fin}(s+1) \hookrightarrow G$ and a proof $hx$ of `GoodScalarKernelTuple selection (1/M) M x`; reals $W \ge 0$, $\tau, \xi, \mathrm{mesh}$; $\mathrm{base} : \mathrm{Fin}\,n_X \to \mathbb Z$; and a finite set $\mathrm{cells}$ of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride`. Write widths $=$ `narrowTrimmedSpatialWidths W τ ξ N`, volume $= \prod_z\prod_i$ `physicalSpatialOutputScale (Fin (s+1)) (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) L_S i`, terms for the type $\mathrm{Fin}\,n_X \to$ `SpatialSiteLabel (Fin (s+1)) spatialModulus 4 mesh`, and twist for `allocatedRecenteredSpatialTwist B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base ℓ` (a complex-valued function of a cell, a term, a site and a point of $\mathbb Z^{n_X}$, defined by OpenAI).
--
--   Hypotheses: $g$ is a complex-valued function of a label $\mathcal P(\mathrm{Fin}(s+1)) \to (\prod_j \mathrm{Fin}\,n_j \to \mathbb Z/\mathrm{period}) \times (\prod_j E_j \to \mathbb Z/\mathrm{period})$, an index $i \in T$, a choice $k$ of one term of each `e a`, a site and a point of LongSpace $\times$ GridSpace, where LongSpace $= (\texttt{JetAmbientIndex (fun _ => Unit) J} \to \mathbb R/\mathbb Z) \times (\Sigma_j J_j \to \mathbb R/\mathbb Z)$ and GridSpace $= \Sigma_j J_j \to \mathbb R/\mathbb Z$, such that `AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g` holds (OpenAI's identity expanding the product of the chart ideal approximation and the full-grid chart model at every physical row sample into products of the $g$-factors); every $g(\cdot,\cdot,\cdot,\mathrm{site},\cdot)$ is $L$-Lipschitz ($L \in \mathbb R_{\ge 0}$) and bounded in norm by $1$; real functions $N_t, V, C_c, H_s$ on the grid axes and $L_g$ with `(e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a)`; $V_{\max} \in \mathbb R_{\ge 0}$ with $V(a) \le V_{\max}$; $\mathrm{stride}_z > 0$; $\mathrm{mesh} > 0$ and $3 + 2\,\mathrm{mesh} \le 4$; `allocatedPhysicalRootBudget B U b S 0` $\le W$; $\mathrm{spatialModulus}\cdot\mathbb Z^{\mathrm{Unit} \oplus \mathrm{Fin}(s+1)}$ is contained in `pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection) (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)` for $\mathrm{root}(g) = x_g(\mathrm{none})$; $\mathrm{widths}(z) > 0$ for every $z$; $\sum_z$ `selectedResidueSmoothWeight stride cells widths z` $> 0$; a signal $\phi : \mathbb Z^{n_X} \to \mathbb C$ with $\|\phi(u)\| \le 1$ on `integerBox N` $= \prod_i [0, N_i)$ and $\phi = 0$ outside it; $\tau > 0$; reals $P_{\mathrm{source}}, P_{\mathrm{volume}} \ge 0$ with $n_X \le P_{\mathrm{source}} + P_{\mathrm{volume}}$ and `integerBoxCubeCount N (s+1)` $/\,\mathrm{volume} \le e^{P_{\mathrm{volume}}}$; reals $\delta, C_{\mathrm{model}}, C_{\mathrm{spatial}} > 0$ with $\sum_{\mathrm{label}}\sum_i\sum_k \|2^{|\mathcal P(\mathrm{Fin}(s+1))|}\cdot$ `allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i` $\cdot$ `coverSiteCoefficient e k`$\| \le C_{\mathrm{model}}$, `allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh` $\le C_{\mathrm{spatial}}$, $\delta \le \mathrm{Re}$ `allocatedRecenteredFiniteModelSource B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference ℓ hM selection hx hW base cells (integerSelfSiteTest (s+1) φ)` (a complex number defined by OpenAI as a cell- and window-weighted sum of the chart model at reconstructed physical points), and $e^{-P_{\mathrm{source}}} \le \delta/(C_{\mathrm{model}}C_{\mathrm{spatial}})$.
--
--   Conclusion: let $A_n$ be the natural number chosen by OpenAI's existence theorem `exists_native_partner_of_physical_cube_mixture_all_degrees s` (universe level $0$) and $Q = (P_{\mathrm{source}} + P_{\mathrm{volume}} + 2)^{A_n}$. There exist a natural number $\mathrm{cover}$ with $0 < \mathrm{cover} \le \mathrm{period}\cdot V_{\max}^{\#\text{grid axes}}$; functions $F_{\mathrm{site}} : (\Sigma_j J_j \to \mathbb R/\mathbb Z) \to \mathbb C$ for $\mathrm{site} \in \mathcal P(\mathrm{Fin}(s+1))$, each Lipschitz with constant $L\cdot\mathrm{period}\cdot V_{\max}^{\#\text{grid axes}}$ and bounded in norm by $1$; and a cell $c \in \mathrm{cells}$ and $t \in$ terms such that, with $\psi(u) = \mathrm{twist}(c, t, \emptyset, u)\cdot F_\emptyset(\texttt{physicalGridFactorInput cover p}\ u)$, we have $\|\psi(u)\| \le 1$ for all $u$, and there exists $\mathcal N$ : `NativeSampleCorrelation (fun _ => 1) s Q (integerBox N) id (fun u => φ u * ψ u)` (OpenAI's structure bundling a rational filtered nilmanifold of degree $s$ and a niltest on it of complexity at most $Q$ correlating with $\phi\psi$ on the box) whose niltest has norm bound at most $1$ and satisfies
--   $$e^{-Q} \le \Bigl\|\mathbb E_{u \in \texttt{integerBox N}}\, \phi(u)\,\overline{\overline{\psi(u)}\;\mathcal N.\mathrm{test}(u)}\Bigr\|.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedNormalizedNativeModel.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B277` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedNormalizedNativeModel.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_native_source)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277

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
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => ((Fin nX) → SpatialSiteLabel (Fin (s + 1)) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference label)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (wholeReference label)
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_native_source_s2
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {Psource Pvolume : ℝ} (hPsource : 0 ≤ Psource) (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ Psource + Pvolume)
    (hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume)
    {δ Cmodel Cspatial : ℝ} (hδ : 0 < δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmodel)
    (hspatial : allocatedSpatialCoefficientCap (Fin nX) selection M spatialModulus mesh ≤ Cspatial)
    (hpositive : δ ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    (hgain : Real.exp (-Psource) ≤ δ / (Cmodel * Cspatial)) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin (s + 1)) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      let ψ := fun u : (Fin nX) → ℤ =>
        twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ)))
      (∀ u, ‖ψ u‖ ≤ 1) ∧
      ∃ V : NativeSampleCorrelation (fun _ : (Fin nX) => 1) s
        ((Psource + Pvolume + 2) ^ Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))
        (integerBox N) id (fun u => signal u * ψ u),
        V.test.normBound ≤ 1 ∧
        Real.exp (-((Psource + Pvolume + 2) ^ Classical.choose
          (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s))) ≤
          ‖𝔼 u ∈ integerBox N, signal u * star (star (ψ u) * V.test.eval u)‖ := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
