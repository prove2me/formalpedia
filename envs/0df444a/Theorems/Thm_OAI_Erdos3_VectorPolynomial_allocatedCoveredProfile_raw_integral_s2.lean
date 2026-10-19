-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoveredProfile_raw_integral_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:14:17.543674+00:00
-- url     : https://prove2.me/theorems/b7ebf05c-e3e2-4176-b53c-dd9287d823b9
-- title:
--   The frozen-source integral of the allocated covered fixed test equals a raw mixed-covered-jet integral against the gridless weighted kernel
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $b_j$ a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ viewed inside the Euclidean space $\mathbb{R}^{J_j}$). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (OpenAI's structure carrying a positive natural number `S.value`). Let $\alpha$ be a type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value`. Write `grid` for OpenAI's predicate `allocatedGridAxis U b S.value` on axes. Let $u$ be a principal axis tuple on the grid axes and $v_0$ one on the non-grid axes (elements of OpenAI's `PrincipalAxisTuples` for the side lengths `allocatedPrincipalSides B U b S`), let $O_j$ be finite types and $\mathrm{rows}_j : O_j \to \operatorname{Finset} \alpha$. Let $Q_j$ be finite types, assume the integer span of $b_j$ equals `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$ (hb), let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, let $bW_j$ be a $\mathbb{Z}$-basis indexed by $Q_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the lattice $\mathbb{Z}^{J_j}$ intersected with `euclideanSubspace (U j)`), and let $d$ be a positive natural number. (All named objects are defined by OpenAI.)
--
--   Write $\lambda$ = `allocatedLongJetReference B U b S O`, the product, over the non-grid axes $a = (j, \cdot)$, of Lebesgue measure on $O_j \to \mathbb{R}$ (for axes $(j, \mathrm{inl}\ \cdot)$) or counting measure on $O_j \to \mathbb{Z}$ (for axes $(j, \mathrm{inr}\ \cdot)$), on the space `AllocatedLongJetRows B U b S O`; $\mu$ = `allocatedFrozenCoefficientSource B U b hR hσ S`, the product over the grid axes of OpenAI's coefficient axis laws, on `AllocatedFrozenCoefficients B U b S`; and $\mathrm{raw}$ = `mixedCoveredJetRawReference d`, the product of the reference measures `mixedArrayReference (I j) (Fin (n j)) (O j)` with the uniform probability on $\prod_j (O_j \to Q_j \to \mathbb{Z}/d)$, on `MixedCoveredJetSource I O Q n d`. Let $f$ be a measurable, $\lambda$-integrable real function on `AllocatedLongJetRows B U b S O`, and $F$ a measurable complex function on `EuclideanJetLayers U O` (the product over $j$ and $O_j$ of the tori `euclideanSubspace (U j)` modulo the lattice section) with $\|F(z)\| \le C$ for all $z$, for some real $C$. Then
--   $$\int \int f(z) \cdot \texttt{allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d}\ (p \mapsto F(p_2))\ a\ z \; d\lambda(z)\, d\mu(a) = \int \texttt{allocatedGridlessWeightedKernel B U b S x u v₀ rows d}\ f_g\ f\ z \cdot F(\texttt{mixedCoveredJetChart U o b hb bW d}\ z) \; d\,\mathrm{raw}(z),$$
--   where `allocatedCoveredFixedTest` is OpenAI's covered fixed test (the deck-mixed test of the reconstruction of the frozen coefficients $a$ and long rows $z$), $f_g$ = `allocatedGridJetDensity B U b hR hσ S x u v₀ rows` (OpenAI's product over grid axes of grid jet factors), `allocatedGridlessWeightedKernel` sends $z$ to $f_g$ of the grid part of $z_1$ times $f$ of the non-grid part of $z_1$ times `coefficientDeckJetDensity root dirs rows d` $z_2$ (with root and directions the `allocatedPhysicalCubeRoot B U b S (fun _ => 0) x` and `allocatedPhysicalCubeDirections B U b S x` of the joined tuple `principalAxisJoin grid u v₀`), and `mixedCoveredJetChart` is OpenAI's chart from mixed covered jet sources to `EuclideanJetLayers U O`. The real values are cast to $\mathbb{C}$ and the integrals are Bochner integrals.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSlicedRowIdealSupport.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedCoveredProfile_raw_integral)

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
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "mixedRef" => Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)
local notation "fg" => allocatedGridJetDensity B U b hR hσ S x u v₀ rows
local notation "fd" => coefficientDeckJetDensity (B := Q) root dirs rows d
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

omit [Fintype α] in
theorem allocatedCoveredProfile_raw_integral_s2
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f)
    (hf : Integrable f longRef)
    (F : EuclideanJetLayers U O → ℂ) (hF : Measurable F)
    {C : ℝ} (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ a, ∫ z, (f z : ℂ) *
      allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d (fun p => F p.2) a z
      ∂longRef ∂allocatedFrozenCoefficientSource B U b hR hσ S) =
    ∫ z, (allocatedGridlessWeightedKernel B U b S x u v₀ rows (Q := Q) d fg f z : ℂ) *
      F (chart z) ∂raw := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
