-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNarrowTrimmed_shifted_vector_site_error
-- name    : OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_shifted_vector_site_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T18:46:29.972269+00:00
-- url     : https://prove2.me/theorems/5c84a50f-ecf0-4914-b849-3c8a0e33361f
-- title:
--   Shifted physical-cube law of the narrow trimmed widths is close to a site approximation
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Write $\mathcal T$ for `PrincipalTupleIndex B (layerSamplerDegree I n)` and $\mathcal V$ for `LayerSamplerVariables G I n B` (whose elements are of the form $\mathrm{inl}\,g$, $g \in G$, or $\mathrm{inr}\,t$, $t \in \mathcal T$). Let $\alpha$ be a finite type with decidable equality, $c : \mathcal V \to \mathbb Z$, $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), and $y, y_0 \in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)`. Put $\mathrm{cols} =$ `principalSpatialColumns (t ↦ c (inr t)) id y` and $\mathrm{refcols}$ the same with $y_0$ (integer matrices indexed by $(\mathrm{Unit} \oplus \alpha) \times \mathcal T$), $\mathrm{ker}(g) = c(\mathrm{inl}\,g) + x_g(\mathrm{none})$, $D =$ `scalarCubeDifferenceMatrix x`, $\mathrm{root} =$ `allocatedPhysicalCubeRoot B U basis S c x y` and $\mathrm{dirs} =$ `allocatedPhysicalCubeDirections B U basis S x y`. Let $\mathrm{selection} : \alpha \hookrightarrow G$, $M \in \mathbb N$, $X$ a finite type, $N, q : X \to \mathbb N$ positive pointwise, and reals $W, \tau, \kappa, C_0, \rho, \xi, \delta, b, r$ with $W \ge 0$, $\tau > 0$, $\kappa > 0$, $\rho > 0$; assume `GoodScalarKernelTuple selection κ M x`, `allocatedPhysicalRootBudget B U basis S c` $\le W$, $1 \le C_0$, $S.\mathrm{value} \le C_0$, $W \le C_0$, $0 < \xi \le 1$, $8(1+W)\,q(d)\,\rho \le \xi\tau N(d)$ for all $d$, and `anisotropicSpatialMeshThreshold selection 𝒯 C₀` $\le \rho$. Let $\mathrm{modulus} \ne 0$ be a natural number such that `integerScalarLattice (Unit ⊕ α) modulus` (the multiples of modulus) is contained in `pivotFullImage (selectedSpatialPivot ker D selection) (selectedSpatialFreeColumns ker D selection)` (the sum of the ranges of these two integer matrices). Let $\mathrm{residue} : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$ with $|\mathrm{residue}(k, d)| \le q(d)$; assume that for every $d$, cols and refcols agree modulo $q(d)\cdot\mathrm{modulus}$; that $0 \le \delta$; and that for all $d$ and $i$, $\sum_t |\mathrm{cols}_{i,t} - \mathrm{refcols}_{i,t}| \le \delta\,H(d)$, where $H(d) =$ `trimmedSpatialRootScale τ N q d` $= \tau N(d)/8/q(d)$. Let $b > 0$, $r > 0$, and $v : X \to (\mathrm{Unit} \oplus \alpha) \to \mathbb Z$ with $|$`spatialStar (v d) i`$/H(d)| \le b$ for all $d, i$ (`spatialStar` adds the $\mathrm{Unit}$ coordinate to every other coordinate). Put $T(d) =$ `trimmedSpatialSlopeScale W τ N q d`, $V =$ `narrowTrimmedSpatialWidths W τ ξ N` (positive by `narrowTrimmedSpatialWidths_pos`), $Q =$ `residueProfileWidth q V` ($Q(k, d) = V(k, d)/q(d)$), $f =$ `canonicalSpatialSiteDensity selection ker D _ W S.value` (the determinant hypothesis supplied by `goodScalarKernelTuple_spatial_det_ne_zero`), $E =$ `anisotropicSpatialError selection 𝒯 M κ C₀ ρ ξ`, $G_0 = \mathrm{modulus}^{|\mathrm{Unit} \oplus \alpha|}$, $\Lambda =$ `anisotropicSpatialDensityLip selection κ` $\cdot (1+W)$, $\mathrm{shift} =$ `physicalResidueOffsetShift root root₀ dirs dirs₀ residue q` (with $\mathrm{root}_0, \mathrm{dirs}_0$ built from $y_0$), and $E' = E + G_0\Lambda\delta$. Let $\nu$ be the image of the probability mass function `smoothProductPMF Q _` on $\mathbb Z^{\mathrm{Option}\,\mathcal V \times X}$ under $z \mapsto \bigl(d \mapsto$ `physicalCubeCoefficient root dirs` $\cdot (k \mapsto z(k, d))\bigr)$ (matrix-vector product). Then
--   $$\Bigl\|\Bigl(\prod_d \prod_i \texttt{physicalSpatialOutputScale}\ \alpha\ H(d)\ T(d)\ S.\mathrm{value}\ i\Bigr)\,\nu(v - \mathrm{shift}) - \prod_d \texttt{spatialSiteApprox}\ P\ F\ \mathrm{modulus}\ f\ H(d)\ b\ r\ (v\,d)\Bigr\| \le |X|\,(E' + 4G_0\Lambda r)\,\bigl(1 + G_0\,\texttt{anisotropicSpatialDensityCap selection}\ \kappa + E'\bigr)^{|X|},$$
--   where $P =$ `selectedSpatialPivot ker D selection`, $F$ is the block matrix `Matrix.fromCols (selectedSpatialFreeColumns ker D selection) (liftResidueMatrix (refcols mod modulus))`, and the real number on the left is cast to $\mathbb C$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedNarrowTrimmed_shifted_vector_site_error` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSpatialProxyCap.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B054` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSpatialProxyCap.lean#L386

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
variable (p : FiniteProbabilityWeights Ω) (label : Ω → R)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open BooleanCubeKernel

namespace BooleanCubeKernel

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
variable (N : X → ℕ) (hN : ∀ x, 0 < N x)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))

variable {dim : ℕ} (root : G ⊕ J → ℤ) (dirs : Matrix (Fin dim) (G ⊕ J) ℤ)
variable (hsite : ∀ s : Finset (Fin dim), (∑ k, |(integerAffineCube root dirs s k : ℝ)|) ≤ W)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (hy : (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).weight y ≠ 0)

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hbudget : allocatedPhysicalRootBudget B U b S c ≤ W)
variable (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedNarrowTrimmed_shifted_vector_site_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ b r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (residue : Option vars × X → ℤ) (hresidue : ∀ k d, |(residue (k,d) : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      δ * trimmedSpatialRootScale τ N q d)
    (hb : 0 < b) (hr : 0 < r) (v : X → (Unit ⊕ α) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ b) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let E := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let shift := physicalResidueOffsetShift root (allocatedPhysicalCubeRoot B U basis S c x y₀)
      dirs (allocatedPhysicalCubeDirections B U basis S x y₀) residue q
    let E' := E + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    ‖(((∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i) *
        (((smoothProductPMF Q hQ).map (fun z d => physicalCubeCoefficient root dirs *ᵥ
          (fun k => z (k, d)))) (v - shift)).toReal : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) b r (v d)‖ ≤
      Fintype.card X * (E' + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
        (1 + G₀ * anisotropicSpatialDensityCap selection κ + E') ^ Fintype.card X := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
