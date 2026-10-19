-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedGridlessWeightedKernel_quarter_support_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedGridlessWeightedKernel_quarter_support_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:17:33.235055+00:00
-- url     : https://prove2.me/theorems/be819ffc-8f79-4224-a582-6d57038286cc
-- title:
--   The allocated gridless weighted kernel is supported in the closed quarter-box region of the mixed covered jet source
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U b R σ` (with scale value `S.value`). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value`. Write grid for `allocatedGridAxis U b S.value`. Let $u$ be an element of `PrincipalAxisTuples grid (allocatedPrincipalSides B U b S)` and $v_0$ an element of `PrincipalAxisTuples (fun a => ¬ grid a) (allocatedPrincipalSides B U b S)`. Let $O_j$ and $Q_j$ be finite types, `rows j : O j → Finset α`, $o_j$ an orthonormal basis (indexed by $I_j$) of the Euclidean copy of $U_j$, and $d$ a nonzero natural number. Let $f_g$ = `allocatedGridJetDensity B U b hR hσ S x u v₀ rows`, the product over the grid axes of OpenAI's integer-matrix-image PMF factors.
--
--   Assume:
--   - $\sigma_j \le 1$ for all $j$;
--   - $T_j$ ($j < m$) are reals with $T_j \ge 0$ and, for every $j$, $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| \cdot 2^{|\alpha|}(|\alpha|+1)^{j+1} \le T_j$;
--   - $C_j$ ($j < m$) are reals with $C_j \ge 0$ such that, for every $j$ and every $v$, $\|\Phi_j^{-1}(v)\| \le C_j \|v\|$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` is the linear isomorphism of $\mathbb{R}^{J_j}$ (Euclidean) with $U_j \times \mathbb{R}^{n_j}$ given by orthogonal projection to $U_j$ and the coordinates in $b_j$ of the projection to $U_j^\perp$, each divided by `basisAxisScale (b j) i`;
--   - for every $j$, $C_j\,\bigl((|I_j| + 1)\,T_j R_j\bigr) \le 1/4$;
--   - $f$ is a real function on `AllocatedLongJetRows B U b S O` (the jet rows on the non-grid axes) such that whenever $f(z) \ne 0$, for every non-grid axis $a$ (in layer $j_a$) and every $t \in O_{j_a}$, $|\texttt{allocatedLongJetRealCoordinates B U b S}\ z\ (a, t)| \le T_{j_a} R_{j_a}$ (these coordinates are the real entries of $z$, with the integer entries on axes $(j, \mathrm{inr}\ i)$ divided by `basisAxisScale (b j) i`).
--
--   Let $z$ be an element of `MixedCoveredJetSource I O Q n d` (that is, for each $j$ a pair of a real array $I_j \times O_j \to \mathbb{R}$ and an integer array $\{0,\dots,n_j-1\} \times O_j \to \mathbb{Z}$, together with residues $O_j \times Q_j \to \mathbb{Z}/d$) such that `allocatedGridlessWeightedKernel B U b S x u v₀ rows d f_g f z` $\ne 0$ (this kernel is $f_g$ of the grid part of $z$, times $f$ of the non-grid part, times OpenAI's coefficient deck jet density of the residue part). Then $z$ lies in `mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))`: after converting the real arrays to coordinates via the orthonormal bases $o_j$, for every $j$ and every $t \in O_j$, the corresponding normalized lattice point (`normalizedLatticePoint (euclideanSubspace (U j)) (b j)`) lies in the closed box $\{y \in \mathbb{R}^{J_j} : |y_i| \le 1/4 \text{ for all } i\}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedGridlessWeightedKernel_quarter_support_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedGridlessWeightedKernel_quarter_support` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedGridlessWeightedKernel_quarter_support)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows

theorem allocatedGridlessWeightedKernel_quarter_support_s2
    (hσ1 : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (f : AllocatedLongJetRows B U b S O → ℝ)
    (hs : ∀ z, f z ≠ 0 → ∀ a : {a // ¬grid a}, ∀ t : O a.val.1,
      |allocatedLongJetRealCoordinates B U b S z ⟨a, t⟩| ≤ T a.val.1 * R a.val.1)
    (z : MixedCoveredJetSource I O Q n d)
    (hz : allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z ≠ 0) :
    z ∈ mixedCoveredJetRegion (E := Q) U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
