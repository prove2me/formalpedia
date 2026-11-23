-- Prove2me | Theorems.Thm_OnlineMaxWeightMatch_Approx_Supplement_lemma_3_1
-- name    : OnlineMaxWeightMatch.Approx.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:24:12.416699+00:00
-- url     : https://prove2.me/theorems/c03c7c5e-9ef2-4153-a2eb-e2f29fb2264c
-- title:
--   Lemma 3.1, p. 6 — approximating MAX-SSAT is PSPACE-hard with no negated random variable and every variable in at most k clauses
-- statement:
--   There exist a constant $k\in\mathbb N$ and a constant $\alpha\in(0,1)$ such that it is PSPACE-hard to compute an $\alpha$-approximation to $OPT_{on}(\phi)$ for MAX-SSAT instances $\phi$ that are 3CNF formulas and satisfy
--
--   1. no random variable appears negated in any clause of $\phi$, and
--   2. each variable, random or deterministic, appears in at most $k$ clauses of $\phi$.
--
--   Here $OPT_{on}(\phi)$ is the maximum expected number of satisfied clauses over adaptive strategies, and an $\alpha$-approximation is any number $a$ with
--   $$\alpha\cdot OPT_{on}(\phi)\le a\le OPT_{on}(\phi).$$
--
--   The lemma extends the hardness result of Condon et al. (Lemma 2.3) by bounding the occurrences of the deterministic variables. The bounded occurrences keep the degrees of the RideHail instance of Theorem 1.1 constant.
--
--   **Formalization Note** The constants $k$ and $\alpha$ are fixed before the reduction, uniformly over all inputs.
--
--   Differences from the source:
--
--   - reading: "PSPACE-hard to compute an α-approximation" → every PSPACE language reduces to it by a polynomial-time instance map and a polynomial-time decoder that decides membership from any rational α-approximation (ApproxHard); reason: the paper does not fix the reduction notion; its proofs use one query per input (Fact 2.1 and the final rescaling), rational answers give a finite numerical interface, the values of these rational finite instances are rational, and the reductions transform rational answers by rational arithmetic
--   - reading: 3CNF formula → every clause has one, two or three literals over x_1, …, x_n; reason: the paper's own formulas φ′ contain the two-literal clauses (2), so 3CNF means at most three literals per clause
--   - encoding: variables x_1, …, x_n with x_1, x_3, … deterministic → Lean variable v is x_{v+1}, so random variables are the odd Lean indices; reason: zero-based indexing; same instances
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 6, Lemma 3.1 (Definition 2.2, pp. 4–5; Lemma 2.3, p. 5)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_ApproxHardness
import Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_MaxSSAT

namespace OnlineMaxWeightMatch.Approx.Supplement

/-- Lemma 3.1: for some constants `k ∈ ℕ` and `α ∈ (0, 1)`, `α`-approximating `OPT_on(φ)` is
PSPACE-hard on 3CNF MAX-SSAT instances with no negated random variable in which every variable
appears in at most `k` clauses. -/
theorem lemma_3_1 :
    ∃ (k : ℕ) (α : ℝ), 0 < α ∧ α < 1 ∧
      ApproxHard encSSAT
        (fun φ => φ.IsThreeCNF ∧ φ.NoNegatedRandom ∧ φ.OccursAtMost k) ssatOpt α := by sorry

end OnlineMaxWeightMatch.Approx.Supplement
