-- Prove2me | Theorems.Thm_OnlinePerceptronIsolation_Binary_theorem_3_1
-- name    : OnlinePerceptronIsolation.Binary.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:14.158888+00:00
-- url     : https://prove2.me/theorems/1623afe5-7696-49e8-ac35-252a389b3d16
-- title:
--   Theorem 3.1 — online algorithms rarely find isolated binary solutions
-- statement:
--   Fix any constraint density $\alpha>0$ and margin $\kappa\in\mathbb R$. Let $h:\mathbb N\to\mathbb R$ satisfy $h(n)/(\log n)^4\to+\infty$, and for each $n$ put $m=\lfloor\alpha n\rfloor$. Let $G\in\mathbb R^{m\times n}$ have independent standard Gaussian entries. For every positive $\varepsilon$, there is an $N$, independent of the algorithm and its seed law, such that
--   $$\forall n\ge N\ \forall A\in\mathrm{ONLINE}(m,n),\qquad \mathbb P_{G,\xi}\bigl(A(G,\kappa;\xi)\in S^{h(n)}(G,\kappa)\bigr)<\varepsilon.$$
--   Here an online algorithm makes jointly measurable, irrevocable sign choices from the observed columns, its previous signs, the margin, and arbitrary internal randomness independent of $G$. The set $S^{h(n)}$ consists of all feasible signings having no other feasible signing at Hamming distance at most $h(n)$. Algorithms may change with $n$. Real radii may exceed $n$ or cross $n$ infinitely often; margins may be zero or negative. No satisfiability, stability, finite-randomness or computational assumption is imposed. This is the full binary-perceptron hardness target, rather than a bound on finding non-isolated solutions.
--
--   Differences from the source:
--   - encoding: one-based sign cube and coordinates → zero-based Fin indices and exact real-valued signs; reason: a bijection of coordinate labels preserves every signing and Hamming distance
--   - encoding: probability over Gaussian inputs and internal randomness → product Gaussian and arbitrary independent seed laws with jointly measurable online sections; reason: this represents the full measurable randomized class and averages over the seed
--   - encoding: the nonnegative success probability is o(1) → for every positive epsilon there is one threshold for all size-n algorithms; reason: the source explicitly provides algorithm-uniformity in Theorem 3.6 and its extension in A.6
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Theorem 3.1, Eq. (3.1), printed p.6, PDF p.8; deduction printed p.12, PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_RandomizedOnline
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary

universe u
/-- Theorem 3.1, printed p.6 / PDF p.8, equation (3.1). Uniform over all online
algorithms and all independent seed laws; the radius is never clipped in the statement. -/
theorem theorem_3_1 (α κ : ℝ) (hα : 0 < α) (h : ℕ → ℝ)
    (hgrowth : Tendsto (fun n => h n / (Real.log n) ^ 4) atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ {Ξ : Type u} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
        (A : Ξ → Fin n → (Fin ⌊α * n⌋₊ × Fin n → ℝ) → ℝ),
        IsRandomizedOnline A → randomSuccess ν A κ (h n) < ε := by sorry

end OnlinePerceptronIsolation.Binary
