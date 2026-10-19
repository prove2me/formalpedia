-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecentered_early_coarse_source_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:21:37.728908+00:00
-- url     : https://prove2.me/theorems/12c55698-0311-4d89-89f9-b3232a3b7bda
-- title:
--   An explicit early coarse mesh for the allocated recentered profile term loses at most exp(-E) from any finer mesh
-- statement:
--   Let $m$ and $\mathrm{dim}$ be natural numbers and $G$ a finite type with decidable equality. For each $j < m$ let $I_j$ and $J_j$ be finite types, $n_j$ a natural number, $U_j$ a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a real basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean subspace given by $U_j$; for each layer sampler axis $a$ (OpenAI's `LayerSamplerAxis I n`) let $B_a$ be a finite type. Let $R, \sigma : \{0,\dots,m-1\} \to \mathbb{R}$ and let $S$ be a layer sampler scale (OpenAI's `LayerSamplerScale B U b R σ`, main field a positive natural number `S.value`). Full tuples are OpenAI's `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides` with sides = `allocatedPrincipalSides B U b S`: for each principal index $t$, a point of the integer cube $\mathrm{Option}\{0,\dots,\mathrm{dim}-1\} \to [-\mathrm{sides}_t, \mathrm{sides}_t) \cap \mathbb{Z}$.
--
--   Let $X$ be a finite type, $\mathrm{modulus}$ a nonzero natural number, $q : X \to \mathbb{N}$ with $q_\xi > 0$ for all $\xi \in X$, and `wholeReference` a function from residue assignments modulo `residueRefinedPeriod modulus q` $= \mathrm{modulus}\cdot\prod_{\xi} q_\xi$ (indexed by principal indices and $\mathrm{Option}\{0,\dots,\mathrm{dim}-1\}$) to full tuples. Let $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`, let $M > 0$ be a natural number and `selection` an embedding $\{0,\dots,\mathrm{dim}-1\} \hookrightarrow G$, and assume `GoodScalarKernelTuple selection (1/M) M x` (OpenAI: the normalized selected minor of the difference matrix $D$ = `scalarCubeDifferenceMatrix x` exceeds $1/M$ in absolute value, and some $a$ with $0 < a \le M$ has $a\,\mathbb{Z}^{\mathrm{dim}} \subseteq D(\mathbb{Z}^{G})$). Let $N : X \to \mathbb{N}$ with $N_\xi > 0$, reals $W, \tau, \xi_0$ with $0 \le W$ and $0 < \tau$, $\mathrm{base} : X \to \mathbb{Z}$, a finite set `cells` of column residue patterns (OpenAI's `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q`), types $O_j$, and a map `point` from $X \to (\mathrm{Unit} \sqcup \{0,\dots,\mathrm{dim}-1\}) \to \mathbb{Z}$ to OpenAI's `EuclideanJetLayers U O` (for each $j$ and each element of $O_j$, a point of the torus of $U_j$ modulo its integer lattice section).
--
--   Let `law` be finite probability weights on full tuples and `profile` a complex function of a full tuple and a point of `EuclideanJetLayers U O`. Let $p, E \ge 0$ be reals with $|G| \le p$, $|X| \le p$, $\mathrm{dim} + 1 \le p$, $M \le e^{p}$, $\mathrm{modulus} \le M^{m+1}$, and the number of layer sampler variables at most $e^{p}$. Assume `allocatedPhysicalRootBudget B U b S (fun _ => 0)` $\le W \le$ (number of layer sampler variables)$\cdot$`S.value` (the left side is OpenAI's root budget, equal here to (number of layer sampler variables)$\cdot$`S.value`, so these two hypotheses together say $W$ equals that product). Assume that $\mathrm{modulus}\cdot\mathbb{Z}^{\mathrm{Unit} \sqcup \{0,\dots,\mathrm{dim}-1\}}$ is contained in `pivotFullImage` of `selectedSpatialPivot root D selection` and `selectedSpatialFreeColumns root D selection` with $\mathrm{root}(g) = 0 + x_g(\mathrm{none})$ (OpenAI; see the statement on the good kernel uniform candidate). Finally assume that the `law`-mean of `allocatedRecenteredProfileMass … profile` (OpenAI: a weighted sum, over the cells, of averaged norms of `profile` at reconstructed points, normalized by a product of spatial scales) is at most `coarseReferenceMassConstant dim X W S.value` $= 4\,(30/\phi(0))^{(\mathrm{dim}+1)|X|}\bigl(((1+W)/\texttt{S.value})^{\mathrm{dim}}\bigr)^{|X|}$, with $\phi$ OpenAI's smooth probability profile.
--
--   Let $\mathrm{coarse}$ = `allocatedEarlyRecenteredMesh X selection M modulus p E` and $T$ = `allocatedEarlyCoarseInput m dim (p + E)` (explicit reals defined by OpenAI). Then $0 < \mathrm{coarse} \le 1/4$, $\mathrm{coarse}^{-1} \le \exp(\texttt{coarseSpatialReciprocalLog}\ T)$, `allocatedSpatialCoefficientCap X selection M modulus coarse` $\le \exp(\texttt{coarseSpatialPartitionLog}\ T)$ (explicit OpenAI quantities), and for every real $\mathrm{fine}$ with $0 < \mathrm{fine} \le \mathrm{coarse}$, every $\mathrm{test} : (X \to (\mathrm{Unit} \sqcup \{0,\dots,\mathrm{dim}-1\}) \to \mathbb{Z}) \to \mathbb{C}$ with $|\mathrm{test}(v)| \le 1$ for all $v$, and every real $\kappa$: if
--   $$\kappa \le \operatorname{Re} \mathbb{E}_{y \sim \mathrm{law}}\, \texttt{allocatedRecenteredProfileTerm}(\ldots, \mathrm{fine}, \ldots, \mathrm{test}, \mathrm{profile})(y),$$
--   then
--   $$\kappa - e^{-E} \le \operatorname{Re} \mathbb{E}_{y \sim \mathrm{law}}\, \texttt{allocatedRecenteredProfileTerm}(\ldots, \mathrm{coarse}, \ldots, \mathrm{test}, \mathrm{profile})(y).$$
--   Here `allocatedRecenteredProfileTerm B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile` (with implicit parameters $\tau$ and $\xi_0$) is OpenAI's complex function of a full tuple $y$: a sum over the cells of a cell weight times a sum, over a spatial window, of a residue spatial kernel at mesh size `mesh` (normalized by a product of spatial scales) times `test` and `profile` evaluated at reconstructed points; the two displays differ only in the mesh argument.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedCoarseSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B194`, `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedCoarseSource.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedRecentered_early_coarse_source_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
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

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

include hq hN hτ in
theorem allocatedRecentered_early_coarse_source_law_s2
    (law : FiniteProbabilityWeights fullTuple)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hMP : (M : ℝ) ≤ Real.exp p) (hmodulus : modulus ≤ M ^ (m + 1))
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ))
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hmass : law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
      B U b S X modulus q wholeReference x N base cells point profile) ≤
        coarseReferenceMassConstant dim X W S.value) :
    let coarse := allocatedEarlyRecenteredMesh X selection M modulus p E
    let T := allocatedEarlyCoarseInput m dim (p + E)
    0 < coarse ∧ coarse ≤ 1 / 4 ∧ coarse⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus coarse ≤ Real.exp (coarseSpatialPartitionLog T) ∧
    ∀ (fine : ℝ), 0 < fine → fine ≤ coarse →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ κ : ℝ,
      κ ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW fine base cells point test profile)).re →
      κ - Real.exp (-E) ≤ (law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW coarse base cells point test profile)).re := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
