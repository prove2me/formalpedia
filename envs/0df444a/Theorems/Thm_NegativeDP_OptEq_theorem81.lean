-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem81
-- name    : NegativeDP.OptEq.theorem81
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:47.493042+00:00
-- url     : https://prove2.me/theorems/f42af937-cb17-45ed-9e54-783519d9bb59
-- title:
--   Theorem 8.1 (N) — a $(p,\varepsilon)$-optimal Markov policy exists
-- statement:
--   In a negative dynamic programming problem, for every probability measure $p$ on $S$ and every $\varepsilon>0$ there is a Markov policy $\pi^*$ that is **$(p,\varepsilon)$-optimal**:
--   $$p\{s : I(\pi^*)(s) \ \ge\ v^*(s) - \varepsilon\} = 1,$$
--   where $v^* = \sup_\pi I(\pi)$ is the supremum over all policies.
--
--   The set in braces need not be Borel; it lies in the completion of the Borel σ-field under $p$. This result is the bridge from the measurability theory of §7 to the optimality equation: applied with $p$ a point mass, it gives Markov policies that are $\varepsilon$-optimal at a given state.
--
--   The paper's Theorem 8.1 has three parts: a stationary policy in the discounted case, a semi-Markov policy in the positive bounded case, and a Markov policy in the negative case. This item is the negative case. **Formalization Note** "$p\{\cdots\}=1$" is stated as "for $p$-almost every $s$", which is the completion reading. The comparison is against $v^*$ over all randomized history-dependent plans; this is the paper's (stronger) notion, not Blackwell's "for each $\sigma$, $p\{I(\pi^*)\ge I(\sigma)-\varepsilon\}=1$".
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 884, Theorem 8.1, case N ((p, ε)-optimality defined on p. 875)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Theorem 8.1, p. 884, negative case: for every probability `p` on `S` and
`ε > 0` there is a `(p, ε)`-optimal Markov policy. -/
theorem theorem81 (P : NegativeDP.Stationary.Problem S A) :
    ∀ p : Measure S, IsProbabilityMeasure p → ∀ ε : ℝ, 0 < ε →
      ∃ πstar : MarkovPlan S A, IsPEOptimal P p ε πstar.toPlan := by sorry

end NegativeDP.OptEq
