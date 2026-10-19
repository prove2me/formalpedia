-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerKernelDensity_output_bounds_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_output_bounds_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:04:32.081973+00:00
-- url     : https://prove2.me/theorems/9cd35841-894c-4183-aaf2-bd15999832d4
-- title:
--   The allocated integer kernel density is bounded and Lipschitz with constant exp(allocatedDensityLog)
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type with decidable equality, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n`, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $\mathrm{basis}_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI, with positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value`. Let $O : \mathrm{Fin}\ m \to \mathrm{Type}$ be a family of finite types with decidable equality, $\mathrm{rows}_j : O_j \to \mathrm{Finset}\ \alpha$, and $s_j$ an embedding of $O_j$ into `BoundedIntegerExponent G (j + 1)` (exponent vectors on $G$ of total degree at most $j+1$), such that for every $j$ the square matrix formed by the columns $s_j(o)$ of the integer jet matrix `scalarKernelIntegerJet x (j + 1) (rows j)` (defined by OpenAI) has nonzero determinant (hypothesis $hA_j$).
--
--   **Hypotheses.** Let $M$ be a natural number with $M > 0$ such that for every $j$, `fixedKernelInverseBound S.positive x (j + 1) (rows j) (s j) (hA j) (1 / M)` holds (a predicate defined by OpenAI: the operator norm of the inverse of the corresponding fixed pivot map is at most an explicit allowance depending on $|\alpha|, |G|, |O_j|$, $j+1$ and $1/M$). Let $P$ be a real number with $0 \le P$, $M \le e^{P}$, and for every $j$: $R_j \le e^{P}$, $R_j^{-1} \le e^{P}$, $\sigma_j^{-1} \le e^{P}$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)}| + 1 \le e^{P}$. Let $u$ be an element of `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)` (integer tuples on the grid axes, defined by OpenAI). Suppose $\sigma_j \le 1$ for all $j$. Let $j \in \mathrm{Fin}\ m$, $i \in \mathrm{Fin}\ (n\ j)$, and let $y$ be a real-valued function on `PrincipalAxisParameter (fun a => ¬ allocatedGridAxis U basis S.value a)` (the parameters of the non-grid axes).
--
--   **Conclusion.** Let $K = \exp(\texttt{allocatedDensityLog B α O P})$, where `allocatedDensityLog` is an explicit real function defined by OpenAI, and let $f$ = `allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y`, a real-valued function on $O_j \to \mathbb{R}$ defined by OpenAI. Then $|f(z)| \le K$ for every $z$, and $f$ is Lipschitz with constant $K$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_output_bounds_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_output_bounds` (in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelOutputRegularity.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B125` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelOutputRegularity.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedIntegerKernelDensity_output_bounds)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125

section

namespace OAI

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

theorem allocatedIntegerKernelDensity_output_bounds_s2 (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j)) (y : input → ℝ) :
    (∀ z, |allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z| ≤ bound) ∧
      LipschitzWith bound (allocatedIntegerKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
