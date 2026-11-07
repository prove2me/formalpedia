-- Prove2me | Theorems.Thm_MultiSelectPandora_fact_3_3
-- name    : MultiSelectPandora.fact_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:18.811049+00:00
-- url     : https://prove2.me/theorems/b13e1e69-1d69-479b-90ac-4a09d289e950
-- title:
--   Fact 3.3 — the Fu–Li–Xu guarantee $\mathrm{OPT}-O(\varepsilon)\mathrm{MAX}$ under (C1)–(C4)
-- statement:
--   There is an absolute constant $C>0$ such that the following holds for every fixed $\varepsilon>0$, every bound $L_0$ on the number of states and every constant $D$. There is a polynomial-time algorithm that, on a stochastic dynamic program with at most $L_0$ states satisfying
--
--   - (C2) the transition is state-monotone,
--   - (C3) the terminal reward is nonnegative and some optimal policy has nonnegative expected marginal reward along its trajectory, and
--   - (C4) $\mathrm{MAX}\le D\cdot\mathrm{OPT}$,
--
--   computes an admissible policy with expected total reward at least
--   $$\mathrm{OPT}-C\varepsilon\,\mathrm{MAX}.$$
--
--   This is the external result that the PTAS applies to the discretized program $I^{SL}$. (C1) is the bound $L_0$.
--
--   Differences from the source:
--   - reading: "polynomial in the input size, that is, in n and the total support size s", in no fixed arithmetic model → Turing.TM2ComputableInPolyTime, polynomial in the binary length of a rational input; reason: the paper fixes no model; a unit-cost model with floor is too strong to mean anything, and a cost monad would need the [FLX18a] program, which this paper does not contain
--   - reading: "computes a policy" → a machine computing the next action from (table, history); reason: an explicit decision tree can have exponential size
--   - encoding: (C1) |V| = O(1) and (C4) MAX = O(OPT) → the bounds L ≤ L₀ and MAX ≤ D·OPT, with L₀, D fixed before the machine; reason: constant size is the quantifier order
--   - encoding: an SSDP with real data → a rational table with L states ordered as integers; reason: a machine reads finite words; p.8 puts the states in this form
--   - reading: "each action can be taken at most once", with end padding and exclusive pairs "the framework allows" → a group has at most two actions, and a repeatable action is a no-op; reason: this is the framework as p.7 states it; the text of [FLX18a] is not available to this mission
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Fact 3.3 ([FLX18a, Theorem 1]) with Definition 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawSSDP
import Definitions.Def_MultiSelectPandora_RawSSDP_Valid
import Definitions.Def_MultiSelectPandora_RawSSDP_C2
import Definitions.Def_MultiSelectPandora_RawSSDP_C3
import Definitions.Def_MultiSelectPandora_RawSSDP_C4
import Definitions.Def_MultiSelectPandora_RawSSDP_Admissible
import Definitions.Def_MultiSelectPandora_RawSSDP_OPT
import Definitions.Def_MultiSelectPandora_RawSSDP_MAX
import Definitions.Def_MultiSelectPandora_RawSSDP_value
import Definitions.Def_MultiSelectPandora_encSSDPIn
import Definitions.Def_MultiSelectPandora_SSDPPolicy
import Definitions.Def_OnlineCRS_Combine_encNat

open OnlineCRS.Combine

namespace MultiSelectPandora

/-- **Fact 3.3 with Definition 3.2**, p.8 (PDF p.9). Beyhaghi–Han–Luqman manuscript, citing [FLX18a, Theorem 1].

For every fixed `ε > 0`, if an instance satisfies (C1)–(C4), a polynomial-time algorithm computes a policy with expected total reward at least `OPT − O(ε) MAX`.

**Formalization Note.** (C1) "`|V| = O(1)`" and (C4) "`MAX = O(OPT)`" are the bounds `L ≤ L₀` and `MAX ≤ D · OPT`, with `L₀` and `D` fixed before the machine, as `ε` is. "Polynomial time" is
Mathlib's `Turing.TM2ComputableInPolyTime`, on binary rational tables and histories, and "computes a policy" is a next-action machine. The statement is checked against p.8 of this paper only. -/
theorem fact_3_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ∀ (L₀ : ℕ) (D : ℝ),
      ∃ next : RawSSDP × List (ℕ × ℕ) → ℕ,
        Nonempty (Turing.TM2ComputableInPolyTime encSSDPIn encNat next) ∧
        ∀ S : RawSSDP, S.Valid → S.L ≤ L₀ → S.C2 → S.C3 → S.C4 D →
          S.Admissible (fun h => next (S, h)) ∧
            S.OPT - C * ε * S.MAX ≤ S.value (fun h => next (S, h)) := by sorry

end MultiSelectPandora
