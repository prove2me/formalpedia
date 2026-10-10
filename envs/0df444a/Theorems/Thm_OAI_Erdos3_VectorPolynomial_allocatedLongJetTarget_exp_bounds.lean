-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedLongJetTarget_exp_bounds
-- name    : OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget_exp_bounds
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:22:01.842017+00:00
-- url     : https://prove2.me/theorems/56258e8a-c70c-4b94-9be4-0179413106f4
-- title:
--   Size and Lipschitz bounds for the allocated long-jet target densities
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type with decidable equality, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality, $x\colon G\to$ `IntegerScalarCubeBox α S.value`, $O_j$ finite types with decidable equality, `rows` $j\colon O_j\to$ `Finset α`, and $s_j\colon O_j\hookrightarrow$ `BoundedIntegerExponent G (j + 1)` such that the square submatrix of `scalarKernelIntegerJet x (j + 1) (rows j)` on the columns $s_j$ has nonzero determinant (`hA`). Let $M>0$ be a natural number (`hM`) with `fixedKernelInverseBound S.positive x (j + 1) (rows j) (s j) (hA j) (1 / M)` for every $j$ (`hi`; this proposition says that the operator norm of the inverse of the normalized pivot map `scalarKernelFixedPivot` is at most `kernelJetInverseAllowance |α| |G| |O j| (j + 1) (1 / M)`). Let $P\ge0$ be real (`hP`) with $M\le e^P$, and for every $j$: $R_j\le e^P$, $R_j^{-1}\le e^P$, $\sigma_j^{-1}\le e^P$ and $|$`BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j + 1)`$|+1\le e^P$ (`hMP`, `hRP`, `hRi`, `hσi`, `hcount`). Let $u\in$ `PrincipalAxisTuples grid (allocatedPrincipalSides B U basis S)`, where grid is the predicate `allocatedGridAxis U basis S.value` on axes, and assume $\sigma_j\le1$ for all $j$ (`hσ1`). Put $\beta=\exp($`allocatedDensityLog B α O P`$)$, where `allocatedDensityLog` is a real number built from `kernelFamilyOutputLog`, $P$ and the numbers `allocatedDensityColumnLog B α j`. Write $T(y,a,z)=$ `allocatedLongJetTarget B U basis S x u rows s hA y a z` for $y\colon$ `PrincipalAxisParameter (¬grid)` $\to\mathbb R$, a non-grid axis $a$ and $z\in$ `CoefficientJetAxisRow O a` ($z\colon O_j\to\mathbb R$ if $a=\langle j,\mathrm{inl}\,i\rangle$, where $T$ is `allocatedContinuousKernelDensity … j i … y z`; $z\colon O_j\to\mathbb Z$ if $a=\langle j,\mathrm{inr}\,i\rangle$, where $T$ is `allocatedIntegerKernelDensity … j i … y` evaluated at $z/$`basisAxisScale (basis j) i`). Then $1\le\beta$; $|T(y,a,z)|\le\beta$ for all $y,a,z$; and for all $a,z$ the map $y\mapsto T(y,a,z)$ is $\beta$-Lipschitz on the closed unit ball about $0$ (sup norm).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedLongJetTarget_exp_bounds` in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedDensityParameterBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedDensityParameterBounds.lean#L501

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

end Erdos3.VectorPolynomial

end

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

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "budget" => allocatedDensityLog (G := G) B α O P
local notation "bound" => NNReal.mk (Real.exp budget) (le_of_lt (Real.exp_pos budget))
local notation "radius" j => NNReal.mk (R j) (le_of_lt (hR j))

include hR hσ hM hi hP hMP hRP hRi hσi hcount

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

theorem allocatedLongJetTarget_exp_bounds (hσ1 : ∀ j, σ j ≤ 1) :
    1 ≤ bound ∧
      (∀ y a z, |allocatedLongJetTarget B U basis S x u rows s hA y a z| ≤ bound) ∧
      (∀ a z, LipschitzOnWith bound
        (fun y => allocatedLongJetTarget B U basis S x u rows s hA y a z) (Metric.closedBall 0 1)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
