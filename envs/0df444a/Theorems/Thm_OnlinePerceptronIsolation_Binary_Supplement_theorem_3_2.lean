-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_Supplement_theorem_3_2
-- name    : OnlinePerceptronIsolation.Binary.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:14:07.522205+00:00
-- url     : https://prove2.me/theorems/1efb259b-b1fd-4085-9d94-dfce45cd36e6
-- title:
--   Theorem 3.2 — online algorithms rarely find isolated general perceptron solutions
-- statement:
--   Fix a constraint density $\alpha>0$ and a well-separated set $K\subseteq\mathbb R$, both independent of $n$. Let $h:\mathbb N\to\mathbb R$ satisfy $h(n)/(\log n)^4\to+\infty$. Put $m=\lfloor\alpha n\rfloor$ and sample $G\in\mathbb R^{m\times n}$ with independent standard Gaussian entries. For every $\varepsilon>0$ there is an $N$, independent of the algorithm and seed law, such that
--   $$\forall n\ge N\ \forall A\in\mathrm{ONLINE}_K(m,n),\qquad\mathbb P_{\xi,G}\{A(\xi,G)\in S^{h(n)}(G,K)\}<\varepsilon.$$
--   An online algorithm makes measurable irrevocable sign choices from the observed columns, its past signs and arbitrary independent internal randomness. Feasibility requires each normalized row score to belong to $K$, and isolation is relative to the entire feasible sign cube. Algorithms may vary with $n$ and have unrestricted time and memory. The family of intervals forming $K$ may be infinite, open, unbounded or include single points. Neither $h(n)<n$ nor existence of isolated solutions is assumed. This companion theorem extends the published binary-perceptron goal to the general model; it is not used in the proof of that goal.
--
--   Differences from the source:
--   - encoding: one-based sign cube and real coordinates → zero-based Fin indices and exact real-valued signs; reason: coordinate relabelling preserves all signings, scores and Hamming distances
--   - encoding: probability over Gaussian inputs and internal randomness → the real value of the product Gaussian measure and arbitrary independent seed laws with jointly measurable online sections; reason: this represents the full randomized class; measure values also give outer probabilities for arbitrary K in the unrestricted supporting lemmas
--   - encoding: the nonnegative success probability is o(1) for any online algorithm → for every positive epsilon, one threshold holds for all size-n algorithms and independent seed laws; reason: the end of §4.3 explicitly makes the deterministic bound algorithm-independent, and the K-version of Lemma A.6 transfers that bound to randomized maps
--   - encoding: a well-separated union of real intervals with one positive separation gap → an arbitrary set-family of order-connected real sets with one shared positive gap; reason: passing from a family to its image as a set of intervals represents every allowed union without a finiteness, closure or nonemptiness restriction
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem 3.2, printed p. 7, PDF p. 9; Eq. (3.2); proof printed pp. 16–17, PDF pp. 18–19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_WellSeparated
import Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_RandomSuccessK
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

universe u
/-- Theorem 3.2, printed p.7 / PDF p.9, equation (3.2). Uniform over all
randomized online maps and independent seed laws, with the full radius-growth domain. -/
theorem theorem_3_2 (α : ℝ) (hα : 0 < α) (K : Set ℝ) (hK : WellSeparated K)
    (h : ℕ → ℝ)
    (hgrowth : Tendsto (fun n => h n / (Real.log n) ^ 4) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {Ξ : Type u} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (A : Ξ → Fin n → (Fin ⌊α * n⌋₊ × Fin n → ℝ) → ℝ),
        IsRandomizedOnline A → randomSuccessK ν A K (h n) < ε := by sorry

end OnlinePerceptronIsolation.Binary.Supplement
