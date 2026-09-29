-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_theorem3
-- name    : LubyMIS.Derandomized.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:59:28.173993+00:00
-- url     : https://prove2.me/theorems/ac7c8119-52d0-4e24-8bb1-4e8778ac1a1c
-- title:
--   THEOREM 3 — E[Y_k − Y_{k+1}] ≥ (1/18)·Y_k with pairwise independent coins of law p′_i
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph with at most $n$ vertices, all of degree $d(i) < n/16$, and let $q$ be a prime with $n \le q \le 2n$. Let $\{\mathrm{coin}(i) : i \in V'\}$ be pairwise independent $\{0,1\}$-valued random variables with $\Pr[\mathrm{coin}(i) = 1] = p'_i = \lfloor q/2d(i)\rfloor / q$ whenever $d(i) \ge 1$, and let $I'$ be Algorithm B's selection for these coins. With $Y_k = |E'|$ and $Y_{k+1}$ the number of edges after the round,
--   $$E[Y_k - Y_{k+1}] \ \ge\ \tfrac{1}{18}\, Y_k .$$
--
--   Applied to the uniform law on the $q^2$ sample points of §4.2, this shows that some sample point eliminates at least $1/18$ of the edges, which is the step Algorithm D takes deterministically.
--
--   **Formalization Note** The page says "the random variables $\{\mathrm{coin}(i)\}$ are as described in this section"; this is read as Lemma D's hypotheses (pairwise independent, marginals $p'_i$), which is what the page's proof ("use Lemma D in place of Lemma B") uses. The graph $G'$ is fixed (conditional expectation given the state). The integrand takes finitely many values, hence is integrable.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, pp. 1046–1047, §4.4, THEOREM 3

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

/-- THEOREM 3 (Luby 1986, §4.4, pp. 1046–1047). If the coins are pairwise independent with
`Pr[coin(i) = 1] = p′_i = ⌊q/2d(i)⌋/q` and every vertex has `d(i) < n/16`, one round of Algorithm B
eliminates in expectation at least `1/18` of the edges: `E[Y_k − Y_{k+1}] ≥ (1/18) Y_k`. -/
theorem theorem3 {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (n q : ℕ) (hq : q.Prime) (hnq : n ≤ q)
    (hq2 : q ≤ 2 * n) (hV : Fintype.card V ≤ n) (hdeg : ∀ i, 16 * H.degree i < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (coin : V → Ω → Bool) (hmeas : ∀ v, Measurable (coin v))
    (hpair : Pairwise fun u v => IndepFun (coin u) (coin v) μ)
    (hmarg : ∀ v, 1 ≤ H.degree v →
      μ.real {ω | coin v ω = true} = ((q / (2 * H.degree v) : ℕ) : ℝ) / q) :
    (∫ ω, (eliminated H (selectB H (fun v => coin v ω)) : ℝ) ∂μ) ≥
      1 / 18 * (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.Derandomized
