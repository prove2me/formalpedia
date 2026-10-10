-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedNormalizedLongJetDensity_zero_off_ball
-- name    : OAI.Erdos3.VectorPolynomial.allocatedNormalizedLongJetDensity_zero_off_ball
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:17:21.430922+00:00
-- url     : https://prove2.me/theorems/efc70694-e901-4314-b9bb-362cc55d65fe
-- title:
--   The normalized long-jet density vanishes outside the jet support ball
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$ with decidable equality, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$ and $\sigma_j > 0$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a finite type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $O_j$ finite types with decidable equality, $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$, and embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that the square submatrix of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)` on the columns $s_j$ has nonzero determinant ($h_A$). Let $M \in \mathbb N$ with $M > 0$, and assume `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for every $j$. Let $P$ be a real with $0 \le P$, $M \le \exp P$, and for every $j$: $R_j \le \exp P$, $R_j^{-1} \le \exp P$, $\sigma_j^{-1} \le \exp P$, and $|$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)`$| + 1 \le \exp P$. Let grid be `allocatedGridAxis U basis S.value` (a predicate on `LayerSamplerAxis I n`), let $u \in$ `PrincipalAxisTuples grid (allocatedPrincipalSides B U basis S)`, let input be the finite type `PrincipalAxisParameter (¬grid)` (with block types $B$ and degrees `layerSamplerDegree I n`, $a \mapsto a.1 + 1$), and let output be $\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}}\, O_{a.1}$. Put $r = \exp($`allocatedJetSupportLog B α O P`$)$. Assume moreover $\sigma_j \le 1$ for all $j$. Then for every $y \in \mathbb R^{\mathrm{input}}$ with $\|y\| \le 1$ and every $v \in \mathbb R^{\mathrm{output}}$ with $r < \|v\|$ (sup norms), `allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v` $= 0$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedNormalizedLongJetDensity_zero_off_ball` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedProxyOutputSupport.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedProxyOutputSupport.lean#L61

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
local notation "radius" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "input" => PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬grid a)
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedNormalizedLongJetDensity_zero_off_ball (hσ1 : ∀ j, σ j ≤ 1)
    (y : input → ℝ) (hy : ‖y‖ ≤ 1) (v : output → ℝ) (hv : radius < ‖v‖) :
    allocatedNormalizedLongJetDensity B U basis S x u rows s hA y v = 0 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
