-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_lemmaC
-- name    : LubyMIS.Derandomized.lemmaC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:57:39.358986+00:00
-- url     : https://prove2.me/theorems/65ff3a3f-08e8-4ecc-9f36-56c846002321
-- title:
--   LEMMA C — Pr[i ∈ N(I′)] ≥ ⅛·min{sum(i), 1} under pairwise independence
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph and let $\{\mathrm{coin}(i) : i \in V'\}$ be $\{0,1\}$-valued random variables on a probability space that are **pairwise** independent, with
--   $$p_i = \Pr[\mathrm{coin}(i) = 1] = \frac{1}{2d(i)} \quad \text{whenever } d(i) \ge 1 .$$
--   Let $I'$ be Algorithm B's selection for these coins. Then for every vertex $i$,
--   $$\Pr[i \in N(I')] \ \ge\ \tfrac18 \cdot \min\{\mathrm{sum}(i), 1\}.$$
--
--   This is the pairwise-independent analogue of Lemma B; the constant drops from Lemma B's $\tfrac14 \min\{\mathrm{sum}(i)/2, 1\}$.
--
--   **Formalization Note** The probability space is arbitrary; the coins are measurable and pairwise independent (`IndepFun` for each pair of distinct vertices), not mutually independent. The coins of vertices of degree $0$ are unconstrained: such vertices are never neighbours of anything and do not affect $N(I')$. The page states the lemma without $d(i) \ge 1$; at $d(i) = 0$ the right side is $0$, so the statement ranges over all $i$.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1045, §4.3, LEMMA C

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

/-- LEMMA C (Luby 1986, §4.3, p. 1045). If the coins `{coin(i)}` are only pairwise independent with
`Pr[coin(i) = 1] = 1/(2d(i))` for `d(i) ≥ 1`, then for Algorithm B's selection `I′`,
`Pr[i ∈ N(I′)] ≥ ⅛ · min {sum(i), 1}`. -/
theorem lemmaC {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (coin : V → Ω → Bool) (hmeas : ∀ v, Measurable (coin v))
    (hpair : Pairwise fun u v => IndepFun (coin u) (coin v) μ)
    (hmarg : ∀ v, 1 ≤ H.degree v → μ.real {ω | coin v ω = true} = 1 / (2 * (H.degree v : ℝ))) (i : V) :
    μ.real {ω | i ∈ nbhd H (selectB H (fun v => coin v ω))} ≥ 1 / 8 * min (sumInv H i) 1 := by sorry

end LubyMIS.Derandomized
