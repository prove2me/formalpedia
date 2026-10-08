-- Prove2me | Theorems.Thm_NegativeDP_EssFinite_vstar_eq_sup_markov
-- name    : NegativeDP.EssFinite.vstar_eq_sup_markov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:45.08373+00:00
-- url     : https://prove2.me/theorems/18b34d16-7cbc-4df4-9b06-51be7b47d769
-- title:
--   Proof of Theorem 8.4, p. 887 — the optimal return is the supremum over Markov policies
-- statement:
--   In Strauch's negative dynamic programming problem (non-empty Borel $S$, $A$, law of motion $q$, Borel return $r\le0$ with $qr>-\infty$), the optimal return $v^*=\sup_\pi I(\pi)$, taken over all randomized history-dependent policies, equals the supremum over non-random Markov policies: for every state $s$,
--   $$\sup_\pi I(\pi)(s)=\sup\{\,I(\hat\pi)(s)\mid \hat\pi \text{ Markov}\,\}.$$
--
--   The paper derives this identity from Theorem 8.1 in the proof of Theorem 8.4, and the proof of Theorem 9.1 uses it in the form "we have shown that $\sup_\pi I(\pi)=\sup_{\pi \text{ Markov}}I(\pi)$". It reduces the search for good policies from history-dependent randomized rules to sequences of measurable maps $S\to A$.
--
--   **Formalization Note** The identity is stated pointwise in $s$, in `EReal`. A Markov policy is a sequence of measurable maps $S\to A$ (`MarkovPlan`), turned into a plan with deterministic kernels by `MarkovPlan.toPlan`; the left side is the model's $v^*$, the supremum over every `Plan`.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 887, proof of Theorem 8.4

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_EssFinite_Model

open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.EssFinite

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Proof of Theorem 8.4, Strauch (1966), p. 887: `sup_π NegativeDP.Stationary.I(π) = sup {NegativeDP.Stationary.I(π̂) | π̂ Markov}`,
pointwise, the left supremum over every randomized history-dependent policy and the right one
over non-random Markov policies. -/
theorem vstar_eq_sup_markov (P : NegativeDP.Stationary.Problem S A) (s : S) :
    NegativeDP.Stationary.vstar P s = ⨆ m : MarkovPlan S A, NegativeDP.Stationary.I P m.toPlan s := by sorry

end NegativeDP.EssFinite
