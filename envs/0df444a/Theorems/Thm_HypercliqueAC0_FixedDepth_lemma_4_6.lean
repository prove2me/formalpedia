-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_6
-- name    : HypercliqueAC0.FixedDepth.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:14:02.957557+00:00
-- url     : https://prove2.me/theorems/d3e0b9fc-ae4e-4aa7-bfb7-5b9057eaedd9
-- title:
--   Lemma 4.6: unique planting and missing edges at every vertex
-- statement:
--   There is an absolute constant $K>0$ such that, for every integer $r\ge2$ and every $0<\delta\le1$, there is $m_0$ depending only on $r,\delta$ with the following property. For $m\ge m_0$, integers $r\le\ell\le m$, a set $A\subseteq[m]$ of cardinality $\ell$, and
--
--   $$0<p\le m^{-(1+\delta)\ell/\binom\ell r},$$
--
--   let $G\sim\mu_p$. Then
--
--   $$\Pr\left[\begin{array}{l}A\text{ is the only }\ell\text{-hyperclique of }G\cup K_A,\\\text{every vertex of }A\text{ lies on an edge of }K_A\text{ absent in }G\end{array}\right]\ge1-Km^{-\delta}.$$
--
--   Both clauses concern the same event. This gives the full uniqueness and coverage target used in the goal theorem.
--
--   **Formalization Note** The proof permits $K=2e^2+1$, so $K$ is quantified before $r,\delta$. The threshold may depend on $r,\delta$ but not on $\ell,p,A$. No separate upper bound $p<1$ is assumed; the printed upper bound supplies it for sufficiently large $m$.
--
--   Differences from the source:
--   - encoding: $[m]=\{1,\ldots,m\}$ and $r$-subsets → $\mathrm{Fin}\,m$ with edge subtype of cardinality $r$; reason: a relabeling bijection preserves the entire hypergraph and all circuit instances
--   - encoding: Boolean-cube Fourier coefficients and product-measure probabilities → Boolean functions converted to real indicators and finite weighted sums over all assignments; reason: the finite product distribution and every coefficient have the same values
--   - reading: $1-O(m^{-\delta})$ → one absolute constant $K>0$ chosen before $r$ and $\delta$, with a threshold after $r,\delta$; reason: the proof bounds failure by $(2e^2+1)m^{-\delta}$, supporting the stronger uniform reading
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.18 (PDF p.20), Lemma 4.6

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 4.6, p.18 (PDF 20). The O constant is absolute, as in its proof.
Both uniqueness and a missing edge through every planted vertex are asserted. -/
theorem lemma_4_6 :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, 2 ≤ r → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (ℓ : ℕ) (p : ℝ) (A : Finset (Fin m)),
        r ≤ ℓ → ℓ ≤ m → 0 < p →
        p ≤ (m : ℝ) ^ (-((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ)) →
        A.card = ℓ →
        probability p (plantedGood (r := r) ℓ A) ≥ 1 - K * (m : ℝ) ^ (-δ) := by sorry

end HypercliqueAC0.FixedDepth
