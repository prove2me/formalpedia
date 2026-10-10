-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernelDensity_output_bounds
-- name    : OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_output_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T23:23:01.717138+00:00
-- url     : https://prove2.me/theorems/77789066-3bfc-489c-bb70-685c3a0c1ab4
-- title:
--   The allocated continuous kernel density is bounded and Lipschitz with an explicit constant
-- statement:
--   The statement uses these section variables (including, through an `include`, several hypotheses that are not mentioned in the conclusion). Let $m \in \mathbb{N}$, $G$ a finite type with decidable equality, $I_j, J_j$ ($j \in \mathrm{Fin}\ m$) finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B_a$ finite types indexed by $a \in$ `LayerSamplerAxis I n` $= \Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$, $U_j \subseteq \mathbb{R}^{J_j}$ real subspaces, and $\mathrm{basis}_j$ a real basis of the orthogonal complement of `euclideanSubspace (U j)` indexed by $\mathrm{Fin}(n_j)$. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with all $R_j > 0$ and $\sigma_j > 0$, and $S$ a `LayerSamplerScale B U basis R σ` (OpenAI's structure: a positive natural number $S.\mathrm{value}$ with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (maps $\mathrm{Option}\ \alpha \to [-S.\mathrm{value}, S.\mathrm{value}) \cap \mathbb{Z}$). Let $O_j$ be finite types with decidable equality, $\mathrm{rows}_j : O_j \to \mathrm{Finset}\ \alpha$, and $s_j$ embeddings of $O_j$ into `BoundedIntegerExponent G (j+1)` (exponent vectors on $G$ of total degree at most $j+1$) such that the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` on the columns $s_j$ has nonzero determinant ($hA_j$). Let $M$ be a positive natural number with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for every $j$ (OpenAI's bound on the norm of the inverse of the fixed pivot map). Let $P \ge 0$ be real with $M \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, and $|$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$| + 1 \le e^P$ for every $j$. Let $u$ be an element of `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)` (OpenAI's type of integer tuples on the non-grid axes). Assume moreover $\sigma_j \le 1$ for all $j$. Then for every $j \in \mathrm{Fin}\ m$, $i \in I_j$ and $y : $ `PrincipalAxisParameter (fun a => ¬ allocatedGridAxis U basis S.value a)` $\to \mathbb{R}$, the function $f = $ `allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y` $: \mathbb{R}^{O_j} \to \mathbb{R}$ (OpenAI's affine selected jet density) satisfies $|f(z)| \le \Lambda$ for all $z$ and is $\Lambda$-Lipschitz, where $\Lambda = \exp($`allocatedDensityLog B α O P`$)$ and `allocatedDensityLog` is an explicit real-valued function of OpenAI.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_output_bounds` in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelOutputRegularity.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelOutputRegularity.lean#L105

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j : Fin m, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [dG : DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedContinuousKernelDensity_output_bounds (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j) (y : input → ℝ) :
    (∀ z, |allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzWith bound (allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
