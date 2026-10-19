-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrowTrimmed_recentered_profile_error_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:19:00.351017+00:00
-- url     : https://prove2.me/theorems/c750a8b4-e12c-41ac-84bf-c3665490fb59
-- title:
--   Under a tuple law, replacing the narrow-trimmed physical-cube profile average by the recentered profile term costs a boundary error plus a spatial error
-- statement:
--   All named objects below are defined by OpenAI.
--
--   **Data.** Let $m$ be a natural number, $G$ a finite type with decidable equality, $I_j$ ($j<m$) finite types with decidable equality, $n : \mathrm{Fin}(m)\to\mathbb{N}$, $B_a$ finite types with decidable equality indexed by `LayerSamplerAxis I n` $= \Sigma_j (I_j \sqcup \mathrm{Fin}(n_j))$, $J_j$ finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, `b j` bases (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, $R, \sigma : \mathrm{Fin}(m)\to\mathbb{R}$, and `S : LayerSamplerScale B U b R σ`. Let $\mathrm{dim}$ be a natural number, write `sides` = `allocatedPrincipalSides B U b S`, $\mathcal{P}$ = `PrincipalTupleIndex B (layerSamplerDegree I n)`, and `fullTuple` = `PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides`. Let $X$ be a finite type, `modulus` a nonzero natural number, $q : X \to \mathbb{N}$, `refined` = `residueRefinedPeriod modulus q`, and `wholeReference` a map from residue labels $\mathcal{P} \to \mathrm{Option}(\mathrm{Fin}\ \mathrm{dim}) \to \mathbb{Z}/\texttt{refined}$ to `fullTuple`. Let $x : G \to$ `IntegerScalarCubeBox (Fin dim) S.value`, $M > 0$ a natural number, `selection : Fin dim ↪ G`, with `GoodScalarKernelTuple selection (1/M) M x`. Let $N : X \to \mathbb{N}$, reals $W, \tau, \xi$ with $W \ge 0$, a real `mesh`, `base : X → ℤ`, a finite set `cells` of `ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q`, families of types $O_j$, a map `point` from $\mathbb{Z}$-valued arrays on $X \times (\mathrm{Unit} \sqcup \mathrm{Fin}\ \mathrm{dim})$ to `EuclideanJetLayers U O`, and a function `test` from such arrays to $\mathbb{C}$. Let $C_0, \rho, \delta$ be reals.
--
--   **Hypotheses on the data.** $N_t > 0$ and $q_t > 0$ for all $t \in X$; $\tau > 0$; $\rho > 0$; `allocatedPhysicalRootBudget B U b S (fun _ => 0)` $\le W$; $1 \le C_0$, $\texttt{S.value} \le C_0$, $W \le C_0$; $0 < \xi \le 1$; $8(1 + W)\,q_t\,\rho \le (\xi\tau)\,N_t$ for all $t$; `anisotropicSpatialMeshThreshold selection 𝒫 C₀` $\le \rho$; $8\cdot$`probabilityProfileLipschitz` $\le \rho$; the lattice `integerScalarLattice (Unit ⊕ Fin dim) modulus` is contained in `pivotFullImage (selectedSpatialPivot (fun g => 0 + x g none) (scalarCubeDifferenceMatrix x) selection) (selectedSpatialFreeColumns … selection)`; $\delta \ge 0$; with $K = |\mathrm{Option}(\texttt{LayerSamplerVariables G I n B})|$ and $e_{\mathrm{phys}} = $ `allocatedPhysicalEntryBudget B U b S (fun _ => 0)`: $2(K\cdot 2e_{\mathrm{phys}}) \le \rho$ and $|\mathcal{P}|\cdot 2e_{\mathrm{phys}} \le \delta\rho$; `mesh` $> 0$; the total mass $\sum_z$ `selectedResidueSmoothWeight q cells V z` is positive, where $V$ = `narrowTrimmedSpatialWidths W τ ξ N`; and $\|\texttt{test}(v)\| \le 1$ for all $v$.
--
--   **Statement.** Let `law` be finite probability weights on `fullTuple` such that every $y$ of nonzero weight satisfies `principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y`. Let `profile : fullTuple → EuclideanJetLayers U O → ℂ`, and let $C_g \ge 0$, $Z > 0$ be reals with $\|\texttt{profile}\ y\ (\texttt{point}\ v)\| \le C_g$ for every $y$ of nonzero weight and every $v$. For a tuple $y$ and an index $z$, let $p_y(z)$ = `physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y) (allocatedPhysicalCubeDirections B U b S x y) base z`, and let
--   $$\mathrm{projected}(y) = \sum_z \pi(z)\cdot \texttt{test}(p_y(z))\cdot \texttt{profile}\ y\ (\texttt{point}(p_y(z))),$$
--   where $\pi$ is the probability mass function `selectedResidueSmoothPMF q cells V hV hmass` (a tsum over $z$). Then
--   $$\Bigl\| \frac{\mathbb{E}_{\texttt{law}}[\mathrm{projected}]}{Z} - \frac{\mathbb{E}_{\texttt{law}}[\mathrm{recentered}]}{Z} \Bigr\| \le \frac{C_g\cdot \mathrm{boundaryError}}{Z} + \frac{\mathrm{spatialError}\cdot \mathbb{E}_{\texttt{law}}[\mathrm{mass}]}{Z},$$
--   where $\mathbb{E}_{\texttt{law}}$ is the (complex, resp. real) mean under `law`; `recentered` = `allocatedRecenteredProfileTerm B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile` (with parameters $\tau, \xi$); `mass` = `allocatedRecenteredProfileMass B U b S X modulus q wholeReference x N base cells point profile` (with parameters $W, \tau, \xi$); $\mathrm{boundaryError} = 24\cdot\texttt{probabilityProfileLipschitz}\cdot |\mathrm{Option}(\texttt{LayerSamplerVariables G I n B}) \times X| / \rho$; and spatialError = `allocatedTupleSpatialError |X| selection 𝒫 M modulus C₀ ρ ξ W δ mesh`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedSpatialToCoarse.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedSpatialToCoarse.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_recentered_profile_error_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

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

local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

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
theorem allocatedNarrowTrimmed_recentered_profile_error_law_s2
    (law : FiniteProbabilityWeights fullTuple)
    (hwhole : ∀ y, law.weight y ≠ 0 →
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg)
    (hcap : ∀ y, law.weight y ≠ 0 → ∀ v, ‖profile y (point v)‖ ≤ Cg) (hZ : 0 < Z) :
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let projected := fun y => ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
          profile y (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U b S x y) base z)))
    ‖law.complexMean projected / (Z : ℂ) -
      law.complexMean (allocatedRecenteredProfileTerm (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x hM selection hx N hW mesh base cells point test profile) / (Z : ℂ)‖ ≤
      Cg * boundaryError / Z + spatialError * law.mean (allocatedRecenteredProfileMass (W := W) (τ := τ) (ξ := ξ)
        B U b S X modulus q wholeReference x N base cells point profile) / Z := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
