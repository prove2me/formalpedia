-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedWholeMaskedCoveredProfile_mean_measurable
-- name    : OAI.Erdos3.VectorPolynomial.allocatedWholeMaskedCoveredProfile_mean_measurable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:15:50.470985+00:00
-- url     : https://prove2.me/theorems/8c7267a1-04a4-44c5-a024-b635081b2f38
-- title:
--   A finite mean of whole masked covered profiles is measurable
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j > 0$ and $\sigma_j > 0$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $\alpha$ be a type with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (integer vectors indexed by $\mathrm{Option}\,\alpha$ with entries in $[-S.\mathrm{value}, S.\mathrm{value})$), $O_j$ finite types, and $\mathrm{rows}_j : O_j \to \mathrm{Finset}\,\alpha$. Assume ($h_b$) that the $\mathbb Z$-span of the range of $b_j$ is `projectedIntegerLattice (euclideanSubspace (U j))` for every $j$; let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, $Q_j$ finite types, $bW_j$ a $\mathbb Z$-basis indexed by $Q_j$ of `latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))` (the integer lattice intersected with that subspace), and $d \ne 0$ a natural number. Let grid be `allocatedGridAxis U b S.value` (a predicate on `LayerSamplerAxis I n`). Let $A$ be a finite type, $p$ a `FiniteProbabilityWeights` on $A$ (a probability vector), $w : A \to$ `PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S)`, $q \in \mathbb N$, and $f : \mathbb R^{\Sigma_{a : \{a \mid \neg\,\mathrm{grid}\,a\}} O_{a.1}} \to \mathbb R$ measurable. Then the function on `EuclideanJetLayers U O`
--   $$y \mapsto \sum_{a \in A} p(a)\,\texttt{allocatedWholeMaskedCoveredProfile}\ B\ U\ b\ h_R\ h_\sigma\ S\ x\ \mathrm{rows}\ h_b\ o\ bW\ d\ (w\,a)\ q\ f\ y,$$
--   viewed as complex-valued, is measurable.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedWholeMaskedCoveredProfile_mean_measurable` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedProductPrefactorCap.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B143` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedSlicedProductPrefactorCap.lean#L188

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B143

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "Output" => (Σ _e : Row, Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "axis" => (fun e : Row => Subtype.val (Prod.snd e))

local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "Output" => (Σ _e : Row, Unit)

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin 1) (Fin.val j + 1))
local notation "BoundedJet" => (Σ a : {a // ¬grid a}, BoundedBooleanJet (Fin 1) (Fin.val (Sigma.fst (Subtype.val a)) + 1))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedWholeMaskedCoveredProfile_mean_measurable
    {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)
    (w : A → PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (q : ℕ) (f : ((Σ a : {a // ¬grid a}, O a.val.1) → ℝ) → ℝ) (hf : Measurable f) :
    Measurable (fun y => (p.mean (fun a =>
      allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d (w a) q f y) : ℂ)) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
