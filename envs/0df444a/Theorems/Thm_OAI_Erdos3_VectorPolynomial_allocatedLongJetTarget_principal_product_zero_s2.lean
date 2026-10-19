-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJetTarget_principal_product_zero_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget_principal_product_zero_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:22:19.745711+00:00
-- url     : https://prove2.me/theorems/002809e5-1042-4159-b28b-0e1670cf96df
-- title:
--   The long-jet target product vanishes outside the long-jet box
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$ with decidable equality; finite types $I_j$ with decidable equality and natural numbers $n_j$; finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n`; finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ and $\sigma_j > 0$; a layer-sampler scale `S : LayerSamplerScale B U basis R σ`; a finite type $\alpha$ with decidable equality and a point $x : G \to $ `IntegerScalarCubeBox α S.value`; a grid tuple $u$ in `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`; finite types $O_j$ with decidable equality and maps $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$; embeddings $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` such that the square integer matrices obtained by restricting the columns of `scalarKernelIntegerJet x (j+1) (rows j)` to $s_j$ have nonzero determinant ($hA$); a positive natural number $M$ with `fixedKernelInverseBound S.positive x (j+1) (rows j) (s j) (hA j) (1/M)` for all $j$; a real $P \ge 0$ with $M \le e^P$, $R_j \le e^P$, $R_j^{-1} \le e^P$, $\sigma_j^{-1} \le e^P$ and $|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)}| + 1 \le e^P$ for all $j$; and the hypothesis $\sigma_j \le 1$ for all $j$. Let grid be the predicate `allocatedGridAxis U basis S.value`, sides $=$ `allocatedPrincipalSides B U basis S`, and $T = \exp(\texttt{allocatedJetSupportLog B α O P})$. Then for every non-grid tuple $v$ in `PrincipalAxisTuples (¬ grid) sides` and every $z$ in `AllocatedLongJetRows B U basis S O` with $z \notin$ `allocatedLongJetBox B U basis S O T`,
--   $$\prod_{a\ \text{non-grid}} \texttt{allocatedLongJetTarget B U basis S x u rows s hA}\ \bigl(\texttt{principalTupleNormalized (principalAxisLength (¬ grid) sides) v}\bigr)\ a\ (z_a) = 0,$$
--   where `allocatedLongJetTarget` is a real function defined by OpenAI and `principalTupleNormalized L v` divides the integer entries of $v$ by the corresponding lengths $L$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget_principal_product_zero_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget_principal_product_zero` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteCoefficientL1.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedFiniteCoefficientL1.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget_principal_product_zero)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
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
variable (hσ1 : ∀ j, σ j ≤ 1)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "T" => Real.exp (allocatedJetSupportLog (G := G) B α O P)

variable (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α)
  (fun a => ¬allocatedGridAxis (I := I) U basis S.value a) (allocatedPrincipalSides B U basis S)))
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "normalized" => principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides)
local notation "target" => (fun (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
  (z : AllocatedLongJetRows B U basis S O) =>
  ∏ a, allocatedLongJetTarget B U basis S x u rows s hA (normalized v) a (z a))

omit [∀ layer, DecidableEq (I layer)] [∀ axis, DecidableEq (B axis)] in
include hR hσ hσ1 hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedLongJetTarget_principal_product_zero_s2
    [∀ layer, DecidableEq (I layer)] [∀ axis, DecidableEq (B axis)]
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (z : AllocatedLongJetRows B U basis S O)
    (hz : z ∉ allocatedLongJetBox B U basis S O T) : target v z = 0 := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
