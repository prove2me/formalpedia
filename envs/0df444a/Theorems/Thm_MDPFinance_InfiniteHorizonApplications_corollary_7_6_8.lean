-- Prove2me | Theorems.Thm_MDPFinance_InfiniteHorizonApplications_corollary_7_6_8
-- name    : MDPFinance.InfiniteHorizonApplications.corollary_7_6_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:01:40.575647+00:00
-- url     : https://prove2.me/theorems/09293798-d277-4935-9381-cb2833e76747
-- title:
--   Corollary 7.6.8 — the Gittins index's optimal-stopping-set, indifference, and bound properties
-- statement:
--   The Gittins index characterizes exactly which quit-rewards make quitting immediately optimal
--   (the optimal stopping set is precisely $\{I(m,n) \le K\}$); at the index itself, continuing and
--   quitting are genuinely *indifferent* ($I(m,n) = J(m,n;I(m,n))$, the indifference property that
--   drives Theorem 7.6.6's proof); the index is always sandwiched between the naive per-period reward
--   rate $p(m,n)/(1-\beta)$ and the maximal possible rate $1/(1-\beta)$; and if the success
--   probability were simply known rather than estimated, the index collapses to the same constant
--   $p/(1-\beta)$ regardless of the observed history — recovering the classical (non-Bayesian) bandit
--   as the degenerate special case.
--
--   **Moderation note.** Part d) is about the $K$-stopping problem of an arm with *known* success probability $p_0$ (`KStoppingValue β (fun _ => p0)`); the draft's rendering "$\forall m,n$, $p(m,n)=p_0$" is false for the Beta-Bernoulli $p$, so the clause was vacuous.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 232, Corollary 7.6.8

import Mathlib
import Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- Corollary 7.6.8 (Bäuerle–Rieder, p. 232, PDF 243). The Gittins-indices have the following
properties: a) The optimal stopping set for the `K`-stopping problem is `\{(m,n) \mid J(m,n;K) =
K\} = \{(m,n) \mid I(m,n) \le K\}`. b) The indifference property: `I(m,n) = J(m,n;I(m,n)) =
p(m,n) + \beta(PJ)(m,n;I(m,n))`. c) `p(m,n)/(1-\beta) \le I(m,n) \le 1/(1-\beta)`. d) If the
success probability is known — the `K`-stopping problem of an arm with constant success
probability `p_0`, `KStoppingValue β (fun _ => p_0)` — then `I(m,n) = p_0/(1-\beta)` (the draft's
rendering `∀ m n, p(m,n) = p_0` is false for the Beta-Bernoulli `p`, making the clause vacuous). -/
theorem corollary_7_6_8 {β : ℝ} (KS : KStoppingValue β pMN) :
    (∀ K m n, KS.J K (m, n) = K ↔ GittinsIndex KS (m, n) ≤ K) ∧
      (∀ m n, GittinsIndex KS (m, n) = KS.J (GittinsIndex KS (m, n)) (m, n) ∧
        GittinsIndex KS (m, n) =
          pMN (m, n) + β * PMN (KS.J (GittinsIndex KS (m, n))) (m, n)) ∧
      (∀ m n, pMN (m, n) / (1 - β) ≤ GittinsIndex KS (m, n) ∧
        GittinsIndex KS (m, n) ≤ 1 / (1 - β)) ∧
      (∀ p0 : ℝ, ∀ KS' : KStoppingValue β (fun _ => p0), ∀ m n,
        GittinsIndex KS' (m, n) = p0 / (1 - β)) := by sorry

end MDPFinance.InfiniteHorizonApplications
