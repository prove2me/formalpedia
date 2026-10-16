-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJetDensity_zero_off_box_v2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-15T22:08:33.644322+00:00
-- url     : https://prove2.me/theorems/700ff86b-b56a-4ce1-81f6-58cf1c60d550
-- title:
--   The allocated long-jet density vanishes outside the long-jet box (copy over the newer bundles)
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$, natural numbers $n_j$, finite types $B_a$ over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; finite types $O_j$ with decidable equality and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that the square integer matrices obtained by restricting the columns of `scalarKernelIntegerJet x (j+1) (rows j)` to $s_j$ have nonzero determinant ($hA$); a positive natural number $M$ with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for all $j$; a real $P \ge 0$ with $M \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`; and the hypothesis $\sigma_j \le 1$ for all $j$. Let grid be the predicate `allocatedGridAxis U basis S.value` and $T = \exp(\texttt{allocatedJetSupportLog B α O P})$. Then for every non-grid tuple $v$ in `PrincipalAxisTuples (¬ grid) (allocatedPrincipalSides B U basis S)` and every $z$ in `AllocatedLongJetRows B U basis S O` (a product, over non-grid axes, of real or integer row arrays) with $z \notin$ `allocatedLongJetBox B U basis S O T` (a product box defined by OpenAI), `allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z` $= 0$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box_v2`, a renamed copy of `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedAmbientLongBox.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B169`, `OAIErdos3B174`, `OAIErdos3B175` of this split (and the bundles they import).
--
--   This is the same statement as `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box`, published earlier in this split, but stated over the definitions bundles `OAIErdos3B169`, `OAIErdos3B174`, `OAIErdos3B175`. Those bundles redeclare the declarations of `OAIErdos3B132`, which `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box` imports, so a lemma built on the newer bundles cannot import `OAI.Erdos3.VectorPolynomial.allocatedLongJetDensity_zero_off_box` and imports this copy instead.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169
import Definitions.Def_OAIErdos3B174
import Definitions.Def_OAIErdos3B175

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

section Box

variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

end Box

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [Fintype α] [DecidableEq α] [DecidableEq G]
variable (x : G → IntegerScalarCubeBox α S.value)
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
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)
local notation "box" => allocatedLongJetBox B U basis S O T

include hR hσ hM hi hP hMP hRP hRi hσi hcount

theorem allocatedLongJetDensity_zero_off_box_v2
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (z : AllocatedLongJetRows B U basis S O) (hz : z ∉ box) :
    allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z = 0 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
