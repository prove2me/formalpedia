-- Prove2me | Theorems.Thm_KendallQueues_GIMs_irreducible_aperiodic
-- name    : KendallQueues.GIMs.irreducible_aperiodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:44:42.118272+00:00
-- url     : https://prove2.me/theorems/cb7b68de-1bc3-44a8-b64e-e1f1d976ac39
-- title:
--   §7, p. 347 — the GI/M/s imbedded chain is irreducible and aperiodic
-- statement:
--   Consider GI/M/s with $s\ge1$ servers, inter-arrival law $A$ on $[0,\infty)$ with mean $a\in(0,\infty)$ and exponential service of mean $b>0$, and let $P=[p_{ij}]$ be the transition matrix (8)–(14) of the imbedded chain. Then for every state $i$:
--
--   1. the transition $i\to0$ has positive probability, $p_{i0}>0$;
--   2. the transition $i\to i+1$ has positive probability, $p_{i,i+1}>0$;
--   3. the diagonal element is positive, $p_{ii}>0$;
--
--   and the chain is irreducible (every state reaches every other state with positive probability in some number of steps) and aperiodic (every state has period $1$).
--
--   Irreducibility and aperiodicity are the hypotheses under which Feller's classification of denumerable chains is applied in the proof of Theorem I.
--
--   **Formalization Note** The chain is any `TransitionMatrix` `P` with `P.p = gimsMatrix s A b`; irreducibility and aperiodicity are the published predicates `Irreducible` and `Aperiodic`. The traffic intensity plays no role here.
-- source:
--   Kendall (Ann. Math. Statist. 24, 1953), §7, p. 347 (irreducibility, (a), (b), aperiodicity)

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_QueueingFundamentals_GM1_EmbeddedChain
import Definitions.Def_QueueingFundamentals_GM1_WaitingTime
import Definitions.Def_KendallQueues_GIMs_Model

open MeasureTheory Filter Topology
open QueueingFundamentals.Foundations QueueingFundamentals.GM1

namespace KendallQueues.GIMs

/-- §7, p. 347: the imbedded chain is irreducible; `i → 0` and `i → i + 1` have positive
probability; the diagonal elements are positive; every state is aperiodic. -/
theorem irreducible_aperiodic (s : ℕ) (hs : 1 ≤ s) (A : Measure ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hA : IsInterarrivalLaw A a⁻¹) (P : TransitionMatrix) (hP : P.p = gimsMatrix s A b) :
    (∀ i, 0 < P.p i 0) ∧ (∀ i, 0 < P.p i (i + 1)) ∧ (∀ i, 0 < P.p i i) ∧
      P.Irreducible ∧ P.Aperiodic := by sorry

end KendallQueues.GIMs
