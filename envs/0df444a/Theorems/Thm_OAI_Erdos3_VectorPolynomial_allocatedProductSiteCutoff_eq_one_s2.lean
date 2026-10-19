-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedProductSiteCutoff_eq_one_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:43:08.445508+00:00
-- url     : https://prove2.me/theorems/1d6b1b32-358a-46a0-911f-027f82935e3b
-- title:
--   The allocated product site cutoff equals one at the chart image of a point whose site values are bounded by r
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$, $J_j$, $E_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and $b_j$ a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be real numbers and $S$ a `LayerSamplerScale B U b R σ`. Let $\alpha$ be a finite type with decidable equality and `rowSets j` a finite set of subsets of $\alpha$ for each $j$; write rowTypes $j$ for the type of elements of `rowSets j`. Let $o_j$ be an orthonormal basis (indexed by $I_j$) of the Euclidean copy of $U_j$; let `hb` be a proof that for each $j$ the $\mathbb{Z}$-span of the range of $b_j$ is the `projectedIntegerLattice` of the Euclidean copy of $U_j$; let `bW j` be a $\mathbb{Z}$-basis, indexed by $E_j$, of the `latticeSection` of the standard lattice $\mathbb{Z}^{J_j}$ in that subspace; let $d$ be a nonzero natural number, and $r$ a nonnegative real with $0 < r$ (proof `hr`). Let chart denote `mixedCoveredJetChart U o b hb bW d`, the map from `MixedCoveredJetSource I rowTypes E n d` to the jet layers `EuclideanJetLayers U rowTypes`.
--
--   Assume:
--   - $R_j > 0$ for all $j$;
--   - $C_j$ ($j < m$) are reals with $C_j \ge 0$ such that, for every $j$ and every $v$, $\|\Phi_j^{-1}(v)\| \le C_j\|v\|$, where $\Phi_j$ = `normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)` is the linear isomorphism of $\mathbb{R}^{J_j}$ (Euclidean) with $U_j \times \mathbb{R}^{n_j}$ given by orthogonal projection to $U_j$ and the $b_j$-coordinates of the projection to $U_j^\perp$, each divided by `basisAxisScale (b j) i`;
--   - for every $j$, $C_j\,\bigl((|I_j| + 1)\,(2rR_j)\bigr) \le 1/4$;
--   - $z$ is an element of `MixedCoveredJetSource I rowTypes E n d` such that for every subset $s \subseteq \alpha$ and every axis $a$,
--   $$\bigl|\texttt{allocatedFullMixedSiteValue U b}\ w_s\ (a)\bigr| \le r,$$
--   where $w_s$ is the $j$-indexed family of (real, integer) pairs obtained from the first component of `mixedCoveredRowsSiteValue rowSets d z s` (the site value of $z$ at $s$, a mixed covered jet source with one row) by regrouping and taking the single row; and `allocatedFullMixedSiteValue U b w` sends the axis $(j, \mathrm{inl}\ i)$ to $(w_j)_1(i)/R_j$ and $(j, \mathrm{inr}\ i)$ to $(w_j)_2(i)\,/\,\texttt{basisAxisScale}(b_j, i)\,/\,R_j$.
--
--   Then `allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z)` $= 1$, where `allocatedProductSiteCutoff` is the product over all subsets $s \subseteq \alpha$ of OpenAI's buffered site chart factors evaluated at the covered rows site value at $s$ (a complex number of norm at most $1$).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductIdealCutoff.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B216` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedProductIdealCutoff.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff_eq_one)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "chart" => mixedCoveredJetChart U o b hb bW d

theorem allocatedProductSiteCutoff_eq_one_s2 (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (z : MixedCoveredJetSource I rowTypes E n d)
    (hbox : ∀ s a, |allocatedFullMixedSiteValue (R := R) U b
      (fun j => mixedArrayRegroup _ _ _ ((mixedCoveredRowsSiteValue rowSets d z s).1 j) ()) a| ≤ (r : ℝ)) :
    allocatedProductSiteCutoff B U b S rowSets o hb bW d r hr (chart z) = 1 := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
