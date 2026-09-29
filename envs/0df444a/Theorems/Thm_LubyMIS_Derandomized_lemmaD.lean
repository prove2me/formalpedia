-- Prove2me | Theorems.Thm_LubyMIS_Derandomized_lemmaD
-- name    : LubyMIS.Derandomized.lemmaD
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T22:58:55.662986+00:00
-- url     : https://prove2.me/theorems/b718da6b-19af-433f-a92a-39bdb98df086
-- title:
--   LEMMA D — Pr[i ∈ N(I′)] ≥ (1/9)·min{sum(i), 1} with the modified probabilities p′_i
-- statement:
--   Let $G' = (V', E')$ be a finite simple graph with at most $n$ vertices, all of degree $d(i) < n/16$, and let $q$ be a prime with $n \le q \le 2n$. Let $\{\mathrm{coin}(i) : i \in V'\}$ be pairwise independent $\{0,1\}$-valued random variables with
--   $$\Pr[\mathrm{coin}(i) = 1] = p'_i = \frac{\lfloor q / 2d(i) \rfloor}{q} \quad \text{whenever } d(i) \ge 1 ,$$
--   and let $I'$ be Algorithm B's selection for these coins. Then for every vertex $i$,
--   $$\Pr[i \in N(I')] \ \ge\ \tfrac19 \min\{\mathrm{sum}(i), 1\}.$$
--
--   This is Lemma C for the rounded probabilities that the $q^2$-point sample space can realize exactly.
--
--   **Formalization Note** $n$ is the number of vertices of the input graph, not of $G'$; the hypothesis $|V'| \le n$ records that $G'$ is a subgraph of it, and $n \le q \le 2n$ with $q$ prime is §4.4's standing choice of $q$. The probability space is arbitrary, with measurable, pairwise independent coins; coins of vertices of degree $0$ are unconstrained. The page prints the closing brace of the minimum as a parenthesis.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1046, §4.4, LEMMA D

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic

open MeasureTheory ProbabilityTheory

namespace LubyMIS.Derandomized

/-- LEMMA D (Luby 1986, §4.4, p. 1046). If the coins are pairwise independent with
`Pr[coin(i) = 1] = p′_i = ⌊q/2d(i)⌋/q` and every vertex has `d(i) < n/16`, then for Algorithm B's
selection `I′`, `Pr[i ∈ N(I′)] ≥ (1/9) min {sum(i), 1}`. -/
theorem lemmaD {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (n q : ℕ) (hq : q.Prime) (hnq : n ≤ q)
    (hq2 : q ≤ 2 * n) (hV : Fintype.card V ≤ n) (hdeg : ∀ i, 16 * H.degree i < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (coin : V → Ω → Bool) (hmeas : ∀ v, Measurable (coin v))
    (hpair : Pairwise fun u v => IndepFun (coin u) (coin v) μ)
    (hmarg : ∀ v, 1 ≤ H.degree v →
      μ.real {ω | coin v ω = true} = ((q / (2 * H.degree v) : ℕ) : ℝ) / q) (i : V) :
    μ.real {ω | i ∈ nbhd H (selectB H (fun v => coin v ω))} ≥ 1 / 9 * min (sumInv H i) 1 := by sorry

end LubyMIS.Derandomized
