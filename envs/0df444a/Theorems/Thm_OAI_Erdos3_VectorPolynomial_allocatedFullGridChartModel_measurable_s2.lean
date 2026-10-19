-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFullGridChartModel_measurable_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_measurable_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:42:16.28605+00:00
-- url     : https://prove2.me/theorems/a4ac1388-d3f5-4907-9998-1dccf24295aa
-- title:
--   The allocated full-grid chart model is measurable
-- statement:
--   Let $m \in \mathbb{N}$; let $G$ be a finite type; let $I_j$ ($j \in \mathrm{Fin}\,m$) be finite types, $n : \mathrm{Fin}\,m \to \mathbb{N}$, and $B_a$ finite types indexed by the sampler axes $a$ in `LayerSamplerAxis I n`; let $J_j$ be finite types, $U_j \subseteq \mathbb{R}^{J_j}$ subspaces, and $b_j$ a basis, indexed by $\mathrm{Fin}(n_j)$, of the orthogonal complement of $U_j$; let $R, \sigma : \mathrm{Fin}\,m \to \mathbb{R}$ and let $S$ be a `LayerSamplerScale B U b R σ` (a structure defined by OpenAI). Let $\alpha$ be a finite type with decidable equality, $\mathrm{rowSets} : \mathrm{Fin}\,m \to \mathrm{Finset}(\mathrm{Finset}\,\alpha)$, $E_j$ finite types, and $d$ a positive natural number. Assume (hypothesis $h_b$) that for each $j$ the $\mathbb{Z}$-span of $b_j$ is the projected integer lattice `projectedIntegerLattice` of $U_j$; let $o_j$ be an orthonormal basis of $U_j$ indexed by $I_j$, and $bW_j$ a $\mathbb{Z}$-basis, indexed by $E_j$, of the section of the standard lattice $\mathbb{Z}^{J_j}$ by $U_j$.
--
--   Let $e$ assign to each grid axis (a sampler axis $a$ with `allocatedGridAxis U b S.value a`, defined by OpenAI) a `ScalarSiteExpansion` over $\mathrm{Finset}\,\alpha$ (a structure defined by OpenAI: a finite type of terms, each with a period, a complex coefficient and a complex-valued factor function), in the same universe as $\alpha$. Then the function
--   $$\texttt{allocatedFullGridChartModel B U b S rowSets d h\_b o bW e} : \texttt{EuclideanJetLayers U rowTypes} \to \mathbb{C}$$
--   is measurable (with respect to the Borel σ-algebras). Here `rowTypes j` is the subtype of $\mathrm{rowSets}_j$, `EuclideanJetLayers U rowTypes` is a real vector space of jet layers defined by OpenAI, and `allocatedFullGridChartModel` (defined by OpenAI) is the complex grid multiplier `allocatedComplexGridMultiplier` applied to the full-grid site approximation built from $e$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_measurable_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_measurable` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedFullGridChartModelMeasurable.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedFullGridChartModelMeasurable.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedFullGridChartModel_measurable)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

theorem allocatedFullGridChartModel_measurable_s2
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) :
    Measurable (allocatedFullGridChartModel B U b S rowSets d hb o bW e) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
