-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJet_variable_test_mean
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongJet_variable_test_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T14:45:29.604107+00:00
-- url     : https://prove2.me/theorems/bc656a86-d4cc-49a0-8f00-a5002e375c18
-- title:
--   Averaged tests of the long jet map against the long jet density
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let grid be the predicate `allocatedGridAxis U basis S.value` on axes and `sides` $=$ `allocatedPrincipalSides B U basis S`. Let $\alpha$ be a finite type with decidable equality, $x\colon G\to$ `IntegerScalarCubeBox α S.value`, and $u$ a tuple in `PrincipalAxisTuples grid sides` (integer tuples over the indices on grid axes). Let $O_j$ be finite types with decidable equality, `rows` $j\colon O_j\to$ `Finset α`, and $s_j\colon O_j\hookrightarrow$ `BoundedIntegerExponent G (j + 1)` (exponents on $G$ of total degree at most $j+1$) such that the square submatrix of `scalarKernelIntegerJet x (j + 1) (rows j)` on the columns $s_j$ has nonzero determinant for every $j$ (`hA`), and assume $\sigma_j\le1$ for all $j$ (`hσ1`). Let $w$ be a `FiniteProbabilityWeights` on `PrincipalAxisTuples (¬grid) sides` (tuples over the non-grid indices), and $\varphi\colon$ `PrincipalAxisTuples (¬grid) sides` $\to$ `AllocatedLongJetRows B U basis S O` $\to\mathbb C$ with each $\varphi(v)$ measurable and $\|\varphi(v,z)\|\le C$ for all $v,z$ (for some real $C$). Then
--   $$\int\sum_v w(v)\,\varphi\big(v,\texttt{allocatedLongJetMap}\ B\ U\ \mathrm{basis}\ S\ x\ u\ v\ \mathrm{rows}\ c\big)\,d\nu(c)=\int\sum_v w(v)\,\texttt{allocatedLongJetDensity}\ \ldots\ x\ u\ v\ \mathrm{rows}\ s\ \mathrm{hA}\ \mathrm{hσ1}\ (z)\cdot\varphi(v,z)\,d\rho(z),$$
--   where $\nu=$ `allocatedLongCoefficientSource B U basis hR hσ S` is the product over axes of the measures `allocatedCoefficientAxisLaw`; $\rho=$ `allocatedLongJetReference B U basis S O` is the product over non-grid axes $a$ of the measures `coefficientJetAxisReference O a`; `AllocatedLongJetRows B U basis S O` assigns to each non-grid axis $a$ an element of `CoefficientJetAxisRow O a`; `allocatedLongJetMap … c` applies `coefficientJetAxisMap` of the matrix `allocatedPartitionedJetMatrix B U basis S x u v rows` to the coefficients at each non-grid axis; and `allocatedLongJetDensity … z` is the real number $\prod_a$ `allocatedLongJetFactor … a (z a)`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongJet_variable_test_mean` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedLongJetMixture.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B134` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedLongJetMixture.lean#L205

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B134

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "source" => allocatedLongCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S O

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedLongJet_variable_test_mean
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides → AllocatedLongJetRows B U basis S O → ℂ)
    (hφ : ∀ v, Measurable (φ v)) {C : ℝ} (hbound : ∀ v z, ‖φ v z‖ ≤ C) :
    (∫ c, w.complexMean (fun v => φ v (allocatedLongJetMap B U basis S x u v rows c)) ∂source) =
      ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v z) ∂reference := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
