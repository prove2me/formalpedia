-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineLongJetProxy_test_integral_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_test_integral_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:14:08.203106+00:00
-- url     : https://prove2.me/theorems/56c96d47-fd74-4d33-9137-0c6689f96948
-- title:
--   Integrating a test function against the allocated affine long-jet proxy density equals its expectation under the normalized long-jet map
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (with scale value `S.value`, a natural number). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (each $x(g)$ is an integer vector indexed by `Option α` with entries in $[-\mathrm{S.value}, \mathrm{S.value})$), and $u$ an element of `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)` (the principal-axis tuples on the grid axes). Let $O_j$ be finite types with decidable equality, `rows j : O j → Finset α`, and `s j` an embedding of $O_j$ into `BoundedIntegerExponent G (j+1)`, such that (`hA`) for every $j$ the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` with columns selected by `s j` has nonzero determinant. Let `center` and `width` be real-valued functions on the active (non-grid) principal-axis parameters `PrincipalAxisParameter … (fun a => ¬ grid a)`.
--
--   Assume further $\sigma_j \le 1$ for all $j$. Let $f$ be a measurable real function on $\mathbb{R}^{\mathrm{realOutput}}$, where realOutput is the index type of pairs $(a, o)$ with $a$ a non-grid axis and $o \in O_j$ for the layer $j$ of $a$. Then
--   $$\int v \mapsto \texttt{allocatedAffineLongJetProxy B U basis S x u rows s hA center width}(v)\, f(v)\; dv = \int f\bigl(\texttt{allocatedNormalizedLongJetMap B U basis S x u rows}\ (i \mapsto \mathrm{center}(i) + \mathrm{width}(i)\, p_2(i))\ p_1\bigr)\, d(\mu \otimes \beta)(p_1, p_2),$$
--   where the left integral is with respect to Lebesgue measure; `allocatedAffineLongJetProxy …` is the density obtained by mixing, over the Boolean source, the affine long-jet densities `allocatedAffineLongJetDensity`; $\mu$ = `unitCoefficientSource activeCoefficient` is the probability measure on $\mathbb{R}^{\mathrm{activeCoefficient}}$ with OpenAI's smooth product density, indexed by `ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid`; and $\beta$ = `jointBooleanSource (fun a => layerSamplerDegree I n a)` is OpenAI's joint Boolean-cube source measure on the active parameters, indexed by the non-grid axes $a$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_test_integral_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_test_integral` (in `lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AllocatedAffineRadiusLog.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedAffineLongJetProxy_test_integral)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "activeInput" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a)
local notation "activeCoefficient" => ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) grid
local notation "realOutput" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) → ℝ)

include hR hσ in
theorem allocatedAffineLongJetProxy_test_integral_s2 (hσ1 : ∀ j, σ j ≤ 1)
    (f : (realOutput → ℝ) → ℝ) (hf : Measurable f) :
    (∫ v, allocatedAffineLongJetProxy B U basis S x u rows s hA center width v * f v) =
      ∫ p : (activeCoefficient → ℝ) × (activeInput → ℝ),
        f (allocatedNormalizedLongJetMap B U basis S x u rows (fun i => center i + width i * p.2 i) p.1)
        ∂(unitCoefficientSource activeCoefficient).prod
          (jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val)) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
