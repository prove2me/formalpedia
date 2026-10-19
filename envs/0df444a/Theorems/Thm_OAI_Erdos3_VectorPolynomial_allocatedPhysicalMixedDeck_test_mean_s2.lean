-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalMixedDeck_test_mean_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:31:40.81156+00:00
-- url     : https://prove2.me/theorems/6677033a-a2e2-4aa6-aad7-c906f0c848b9
-- title:
--   The physical mixed-deck test mean over the coefficient source equals the frozen-source integral of the weighted long-jet density times the deck mixed test
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types with decidable equality, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type with decidable equality to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$, $a \in I_j \sqcup \operatorname{Fin} n_j$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $b_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ viewed inside $\mathbb{R}^{J_j}$), $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U b R σ` (OpenAI's structure with a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value`, and write `grid` for OpenAI's predicate `allocatedGridAxis U b S.value` on axes and `sides` for `allocatedPrincipalSides B U b S`. Let $u$ be a principal axis tuple on the grid axes and $v_0$ one on the non-grid axes (elements of OpenAI's `PrincipalAxisTuples`), $O_j$ finite types with decidable equality, $\mathrm{rows}_j : O_j \to \operatorname{Finset} \alpha$, $Q_j$ finite types and $d$ a positive natural number. Let $\varphi$ be a complex function on triples $((a_0, t), r)$ with $a_0 \in$ `AllocatedFrozenCoefficients B U b S` (coefficient rows of the grid axes), $t \in \prod_j (I_j \to O_j \to \mathbb{R}) \times (\operatorname{Fin} n_j \to O_j \to \mathbb{Z})$ and $r \in \prod_j (O_j \to Q_j \to \mathbb{Z}/d)$. For each $j$ let $s_j$ be an embedding of $O_j$ into `BoundedIntegerExponent G (j+1)` such that the square submatrix on the columns $s_j$ of `scalarKernelIntegerJet x (j+1) rows_j` has nonzero determinant (hA), and assume $\sigma_j \le 1$ for all $j$ (hσ1). (All named objects are defined by OpenAI.)
--
--   Let `weights` be finite probability weights on the principal axis tuples of the non-grid axes, let $M$ be a natural number such that for every $j$ the lattice $M \cdot \mathbb{Z}^{O_j}$ is contained in the image of `scalarKernelIntegerJet x (j+1) rows_j` (hperiod), and assume every $v$ of nonzero weight has `principalResidueLabel M v` $=$ `principalResidueLabel M v₀` (the coordinates of $v$ and $v_0$ agree modulo $M$) (hresidue). Assume $\varphi$ is measurable and $\|\varphi(p)\| \le C$ for all $p$, for some real $C$. For a non-grid tuple $v$ write $\mathrm{root}(v)$, $\mathrm{dirs}(v)$ for `allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)` and `allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)`. Then
--   $$\int \mathbb{E}_{v}\, \varphi\Bigl(\bigl((\texttt{split}\ p_1)_1,\ \texttt{canonicalCoefficientJetArrays}\ (\mathrm{root}\ v)\ (\mathrm{dirs}\ v)\ \mathrm{rows}\ p_1\bigr),\ \texttt{coefficientDeckJetMap}\ (\mathrm{root}\ v)\ (\mathrm{dirs}\ v)\ \mathrm{rows}\ d\ p_2\Bigr)\, d(\mathrm{source} \otimes \mathrm{deck})(p)$$
--   $$= \int \int \mathbb{E}_v\bigl[\texttt{allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1}\ z\bigr] \cdot \texttt{allocatedDeckMixedTest B U b S x u v₀ rows Q d φ}\ a_0\ \bigl(\texttt{allocatedMixedJetReconstruct B U b S x u v₀ rows}\ a_0\ z\bigr)\, d\lambda(z)\, d\mu(a_0).$$
--   Here $\mathbb{E}_v$ is the mean with respect to `weights` (the real mean cast to $\mathbb{C}$ in the second line); `source` = `allocatedCoefficientSource B U b hR hσ S` is the product of OpenAI's mixed scalar array laws on the coefficient sampler arrays; `deck` is the uniform probability on `CoefficientDeckResidues Q d` (for each $j$, functions from bounded coefficient exponents of degree $j+1$ and $Q_j$ to $\mathbb{Z}/d$); `split` = `allocatedCoefficientSplit B U b S` splits a sampler array into its grid part and its long part; `canonicalCoefficientJetArrays` applies the bounded coefficient jet matrices to the arrays and `coefficientDeckJetMap` applies them to the deck residues; $\lambda$ = `allocatedLongJetReference B U b S O` (the product, over non-grid axes, of Lebesgue measure for axes $(j, \mathrm{inl}\ \cdot)$ and counting measure for axes $(j, \mathrm{inr}\ \cdot)$); $\mu$ = `allocatedFrozenCoefficientSource B U b hR hσ S` (the product of the coefficient axis laws over grid axes); `allocatedLongJetDensity` is OpenAI's product of long-jet factors; `allocatedDeckMixedTest ... a₀ t` is the integral of $\varphi((a_0, t), \texttt{coefficientDeckJetMap}\ (\mathrm{root}\ v_0)\ (\mathrm{dirs}\ v_0)\ \mathrm{rows}\ d\ r)$ over $r \sim$ deck; and `allocatedMixedJetReconstruct` reassembles full jet arrays from $a_0$ (via OpenAI's frozen jet map) and the long rows $z$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredFixedTest.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B194` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredFixedTest.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedDeck_test_mean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable (φ : (AllocatedFrozenCoefficients B U b S ×
  (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))) × (∀ j, O j → Q j → ZMod d) → ℂ)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalMixedDeck_test_mean_s2
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, weights.weight v ≠ 0 → principalResidueLabel M v = principalResidueLabel M v₀)
    (hφ : Measurable φ) {C : ℝ} (hbound : ∀ p, ‖φ p‖ ≤ C) :
    (∫ p, weights.complexMean (fun v =>
      φ (((split p.1).1, canonicalCoefficientJetArrays (root v) (dirs v) rows p.1),
        coefficientDeckJetMap (root v) (dirs v) rows d p.2)) ∂(source).prod (deck).toMeasure) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          allocatedDeckMixedTest B U b S x u v₀ rows Q d φ a₀
            (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
