-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_theorem2
-- name    : LubyMIS.Derandomized.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:58:08.958369+00:00
-- url     : https://prove2.me/theorems/e1bb0b80-03e3-454b-965c-0ad04bc453bc
-- title:
--   THEOREM 2 — E[Y_k − Y_{k+1}] ≥ (1/16)·Y_k for pairwise independent coins
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph and let $\{\mathrm{coin}(i) : i \in V'\}$ be pairwise independent $\{0,1\}$-valued random variables with $\Pr[\mathrm{coin}(i) = 1] = 1/2d(i)$ whenever $d(i) \ge 1$. Let $I'$ be Algorithm B's selection for these coins, and let $Y_k = |E'|$ and $Y_{k+1}$ be the numbers of edges before and after the round. Then
--   $$E[Y_k - Y_{k+1}] \ \ge\ \tfrac{1}{16}\, Y_k .$$
--
--   A round of Algorithm B thus removes a constant fraction of the edges in expectation even when its coins are only pairwise independent, which is what allows them to be drawn from a small sample space.
--
--   **Formalization Note** The current graph $G'$ is fixed, so the expectation is the conditional one given the state before the round, which is what the proof establishes. $Y_k - Y_{k+1}$ is the number of edges with an endpoint in $I' \cup N(I')$; it takes finitely many values, hence is integrable. The probability space is arbitrary, with measurable, pairwise independent coins.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1046, §4.3, THEOREM 2

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

/-- THEOREM 2 (Luby 1986, §4.3, p. 1046). If the coins `{coin(i)}` are only pairwise independent with
`Pr[coin(i) = 1] = 1/(2d(i))` for `d(i) ≥ 1`, one round of Algorithm B eliminates in expectation at
least `1/16` of the edges: `E[Y_k − Y_{k+1}] ≥ (1/16) Y_k`. -/
theorem theorem2 {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (coin : V → Ω → Bool) (hmeas : ∀ v, Measurable (coin v))
    (hpair : Pairwise fun u v => IndepFun (coin u) (coin v) μ)
    (hmarg : ∀ v, 1 ≤ H.degree v → μ.real {ω | coin v ω = true} = 1 / (2 * (H.degree v : ℝ))) :
    (∫ ω, (eliminated H (selectB H (fun v => coin v ω)) : ℝ) ∂μ) ≥
      1 / 16 * (H.edgeFinset.card : ℝ) := by sorry

end LubyMIS.Derandomized
