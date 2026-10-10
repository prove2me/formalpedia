-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalMixedJet_test_mean
-- name    : OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedJet_test_mean
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T23:19:52.312474+00:00
-- url     : https://prove2.me/theorems/ae5ce1c8-2884-4c61-81a3-f8d188e1154b
-- title:
--   The physical mixed-jet test mean equals a long-jet density integral
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$) with decidable equality, $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ with decidable equality indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$ and $\sigma_j > 0$ with $\sigma_j \le 1$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$). Let grid be `allocatedGridAxis U b S.value` (a predicate on `LayerSamplerAxis I n`) and sides be `allocatedPrincipalSides B U b S`; let $u \in$ `PrincipalAxisTuples grid sides` and $v_0 \in$ `PrincipalAxisTuples (¬grid) sides`. Let $O_j$ be finite types with decidable equality, $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$, and $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` embeddings such that the square submatrix of the integer matrix `scalarKernelIntegerJet x (j+1) (rows j)` on the columns $s_j$ has nonzero determinant ($h_A$). Let weights be `FiniteProbabilityWeights` (a probability vector $w$) on `PrincipalAxisTuples (¬grid) sides`, and let $\varphi$ assign to each $a_0 \in$ `AllocatedFrozenCoefficients B U b S` and each family $t = (t_j)_j$ with $t_j \in \mathbb R^{I_j \times O_j} \times \mathbb Z^{\mathrm{Fin}(n_j) \times O_j}$ a complex number, with $(a_0, t) \mapsto \varphi(a_0, t)$ measurable and $\|\varphi(a_0, t)\| \le C$ for all $a_0, t$, for a real $C$. For $v$ write $\mathrm{root}(v) =$ `allocatedPhysicalCubeRoot B U b S 0 x (principalAxisJoin grid u v)` and $\mathrm{dirs}(v) =$ `allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)`, where `principalAxisJoin` glues $u$ and $v$ into one tuple. Let source be `allocatedCoefficientSource B U b hR hσ S`, frozenSource be `allocatedFrozenCoefficientSource B U b hR hσ S`, reference be `allocatedLongJetReference B U b S O`, and split be the measurable equivalence `allocatedCoefficientSplit B U b S`. Then
--   $$\int \sum_v w(v)\,\varphi\bigl((\mathrm{split}\,a)_1,\ \texttt{canonicalCoefficientJetArrays}\ \mathrm{root}(v)\ \mathrm{dirs}(v)\ \mathrm{rows}\ a\bigr)\,d\,\mathrm{source}(a)$$
--   equals
--   $$\int\!\!\int \Bigl(\textstyle\sum_v w(v)\,\texttt{allocatedLongJetDensity}\ B\ U\ b\ h_R\ h_\sigma\ S\ x\ u\ v\ \mathrm{rows}\ s\ h_A\ h_{\sigma 1}\ z\Bigr)\cdot\varphi\bigl(a_0,\ \texttt{allocatedMixedJetReconstruct}\ B\ U\ b\ S\ x\ u\ v_0\ \mathrm{rows}\ a_0\ z\bigr)\,d\,\mathrm{reference}(z)\,d\,\mathrm{frozenSource}(a_0),$$
--   the real density mean being cast to $\mathbb C$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedPhysicalMixedJet_test_mean` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredFixedTest.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B132` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredFixedTest.lean#L195

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B169

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O B : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Fintype (B j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "join" => MeasurableEquiv.piEquivPiSubtypeProd (CoefficientJetAxisRow O) grid
local notation "split" => allocatedCoefficientSplit B U b S
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

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
variable (rows : ∀ j, O j → Finset α) (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedPhysicalMixedJet_test_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : AllocatedFrozenCoefficients B U b S →
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) → ℂ)
    (hφ : Measurable (fun p : AllocatedFrozenCoefficients B U b S ×
      (∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) => φ p.1 p.2))
    {C : ℝ} (hbound : ∀ a t, ‖φ a t‖ ≤ C) :
    (∫ a, weights.complexMean (fun v => φ (split a).1
      (canonicalCoefficientJetArrays (root v) (dirs v) rows a)) ∂source) =
      ∫ a₀, ∫ z,
        (weights.mean (fun v => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z) : ℂ) *
          φ a₀ (allocatedMixedJetReconstruct B U b S x u v₀ rows a₀ z) ∂reference ∂frozenSource := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
