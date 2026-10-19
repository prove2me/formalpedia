-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedCoveredProfileDensity_lintegral_abs_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:15:44.812247+00:00
-- url     : https://prove2.me/theorems/0b11aa01-49ce-4d93-bce7-44876d91148c
-- title:
--   The covered profile density of an integrable function has L1 norm at most that of the function
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$, $J_j$, $O_j$, $Q_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$, let `euclideanSubspace (U j)` be that subspace in the Euclidean space $\mathbb{R}^{J_j}$ (defined by OpenAI), let $b_j$ be a real basis, indexed by $\operatorname{Fin} n_j$, of its orthogonal complement whose integer span equals `projectedIntegerLattice` (the projection of $\mathbb{Z}^{J_j}$ onto that complement; hypothesis hb), let $o_j$ be an orthonormal basis of `euclideanSubspace (U j)` indexed by $I_j$, and let $bW_j$ be a $\mathbb{Z}$-basis, indexed by $Q_j$, of `latticeSection` (the lattice $\mathbb{Z}^{J_j} \cap$ `euclideanSubspace (U j)`), which is assumed to be a full lattice. Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$, and let $S$ be a `LayerSamplerScale B U b R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\alpha$ be a type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\ \alpha \to [-\texttt{S.value}, \texttt{S.value}) \cap \mathbb{Z}$). Write `grid` for OpenAI's predicate `allocatedGridAxis U b S.value` on axes; let $u$ be a principal integer tuple on the grid axes and $v$ one on the non-grid axes (with side lengths `allocatedPrincipalSides B U b S`). Let `rows j` $: O_j \to$ finite subsets of $\alpha$. Let $d \ne 0$ be a natural number. Let $\Omega_j(t) \subseteq \mathbb{R}^{J_j}$, for $j \in \operatorname{Fin} m$ and $t \in O_j$, be measurable sets each contained in `standardLatticeSmallBox` $= \{y : |y_i| < 1/2 \text{ for all } i\}$. Let $\nu_j$ be left-invariant probability measures on the quotient of `euclideanSubspace (U j)` by `latticeSection`, and let `haar` be the product measure $\prod_j \prod_{t \in O_j} \nu_j$ on `EuclideanJetLayers U O`.
--
--   Let `reference` = `allocatedLongJetReference B U b S O`, OpenAI's product reference measure on `AllocatedLongJetRows B U b S O` (one coefficient jet row for each non-grid axis), and let $f$ be a real function on `AllocatedLongJetRows B U b S O` that is integrable with respect to `reference`. Let `profile f` = `allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω f`, OpenAI's density on `EuclideanJetLayers U O` obtained by pushing forward, through the chart `mixedCoveredJetChart U o b hb bW d` restricted to the region `mixedCoveredJetRegion U o b d Ω`, the function $z \mapsto (\text{fixed factor at } z) \cdot f(\text{non-grid part of } z)$. Then
--   $$\int^{-} \operatorname{ofReal}\bigl|\texttt{profile } f\ (y)\bigr| \, d\,\texttt{haar}(y) \le \operatorname{ofReal}\Bigl(\int |f(z)| \, d\,\texttt{reference}(z)\Bigr),$$
--   where the left side is a lower Lebesgue integral in $[0, \infty]$ and $\operatorname{ofReal}$ maps a real number to $[0, \infty]$ (negative numbers to $0$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredSiteExpansion.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedCoveredSiteExpansion.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedCoveredProfileDensity_lintegral_abs)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω

variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "reference" => allocatedLongJetReference B U b S O

include hΩm hΩ in
theorem allocatedCoveredProfileDensity_lintegral_abs_s2
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Integrable f reference) :
    (∫⁻ y, ENNReal.ofReal |profile f y| ∂haar) ≤ ENNReal.ofReal (∫ z, |f z| ∂reference) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
