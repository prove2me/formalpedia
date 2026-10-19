-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousKernelDensity_zero_off_box_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_zero_off_box_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:42:30.138287+00:00
-- url     : https://prove2.me/theorems/6bdf6196-9717-47c3-af5b-932b18791c74
-- title:
--   The allocated continuous kernel density vanishes outside the jet-support radius
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type with decidable equality, and for $j < m$ let $I_j$, $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (with scale value `S.value`, a positive natural number). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (each $x(g)$ is an integer vector indexed by `Option α` with entries in $[-\mathrm{S.value}, \mathrm{S.value})$). Let $O_j$ be finite types with decidable equality, `rows j : O j → Finset α`, and `s j` an embedding of $O_j$ into `BoundedIntegerExponent G (j+1)`, such that (`hA`) for every $j$ the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` with columns selected by `s j` has nonzero determinant. Let $M$ be a natural number and $P$ a real number, and assume:
--   - $0 < M$;
--   - for every $j$, `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` holds (the operator norm of the inverse of the fixed pivot map `scalarKernelFixedPivot` is at most `kernelJetInverseAllowance |α| |G| |O_j| (j+1) (1/M)`);
--   - $0 \le P$, $M \le e^P$, and for every $j$: $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$, and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$.
--
--   Let $u$ be an element of `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`. Assume moreover $\sigma_j \le 1$ for all $j$. Let $j < m$, $i \in I_j$, let $y$ be a real-valued function on the active (non-grid) principal-axis parameters `PrincipalAxisParameter … (fun a => ¬ grid a)` with sup norm $\|y\| \le 1$, and let $z \in \mathbb{R}^{O_j}$ with
--   $$\exp\bigl(\texttt{allocatedJetSupportLog B α O P}\bigr) < \|z\|$$
--   (sup norm), where `allocatedJetSupportLog B α O P` $= \texttt{allocatedDensityLog B α O P} + P + \sum_{j<m}\bigl(|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + |\alpha|\,(j+2)\bigr)$. Then
--   $$\texttt{allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j)}\ y\ z = 0,$$
--   where `allocatedContinuousKernelDensity` is OpenAI's affine selected-jet density for layer $j$ and axis $i$, evaluated at parameter $y$ and output $z$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_zero_off_box_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_zero_off_box` (in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelSupport.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B176` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedKernelSupport.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedContinuousKernelDensity_zero_off_box)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B176

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
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m,
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "outputRadius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

include hR hσ hM hi hP hMP hRP hRi hσi hcount

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedContinuousKernelDensity_zero_off_box_s2 (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : I j)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ)
    (hy : ‖y‖ ≤ 1) (z : O j → ℝ) (hz : outputRadius < ‖z‖) :
    allocatedContinuousKernelDensity B U basis S j i x u (rows j) (s j) (hA j) y z = 0 := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
