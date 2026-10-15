-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_theorem_1_2
-- name    : OnlineMaxWeightMatch.Approx.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:47.786977+00:00
-- url     : https://prove2.me/theorems/23325790-1e04-4256-8327-2ee4587b53ae
-- title:
--   Theorem 1.2: rounding LP-Match online earns 0.51 of the optimal online algorithm
-- statement:
--   Let $I$ be a RideHail instance: bins $i$ (a finite set), balls $t=1,\dots,n$ arriving in this order, ball $t$ arriving independently with probability $p_t\in[0,1]$, and weights $w_{i,t}\ge 0$. Let $\mathrm{OPT}_{on}(I)$ be the expected profit of the optimal online algorithm, and let $x$ be any optimal solution of the linear program LP-Match. Then Algorithm 1 (Rounding LP-Match Online, with $c=0.01$) run on $x$ satisfies
--
--   $$
--   \mathbb E\Big[\sum_{(i,t)\in M}w_{i,t}\Big]\ \ge\ 0.51\cdot \mathrm{OPT}_{on}(I),
--   $$
--
--   where $M$ is the matching it outputs.
--
--   The paper states: "There exists a polynomial-time online algorithm which is a 0.51-approximation of the optimal online algorithm for the RideHail problem." The algorithm is Algorithm 1; the benchmark is the optimal **online** algorithm, not the offline optimum, against which $1/2$ cannot be beaten.
--
--   **Formalization Note** "Polynomial time" is not formalized. Stating only that *some* online algorithm earns $0.51\cdot\mathrm{OPT}_{on}(I)$ would be trivially true (take the optimal online algorithm), so the theorem names Algorithm 1 run on an arbitrary optimal LP-Match solution $x$, which is what the paper's proof uses. The constant is $0.51=1/2+c$. Only the lower end of the paper's "$\alpha$-approximation" ($A(I)\in[\alpha Q,Q]$) is stated: the upper end holds because Algorithm 1 is itself an online algorithm. $\mathrm{OPT}_{on}$ is the supremum over deterministic non-anticipating online policies; Algorithm 1's expected profit is defined with the dummy bins of Line 2 (weight $0$).
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 2, Theorem 1.2 (restated p. 10; proof p. 11)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Algorithm1

open MeasureTheory ProbabilityTheory

namespace OnlineMaxWeightMatch.Approx

/-- Theorem 1.2. Algorithm 1, run on any optimal solution `x` of LP-Match, is a
`0.51`-approximation of the optimal online algorithm: its expected profit is at least
`0.51 · OPT_on(I)`. -/
theorem theorem_1_2 {ι : Type*} [Fintype ι] {n : ℕ} (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) (hopt : IsLPOptimal I x) :
    51 / 100 * optOn I ≤ algorithm1Value I x := by sorry

end OnlineMaxWeightMatch.Approx
