-- Prove2me | Theorems.Thm_MultiSelectPandora_claim_3_1
-- name    : MultiSelectPandora.claim_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:16:03.903201+00:00
-- url     : https://prove2.me/theorems/65512683-7f59-4484-8527-937ff7875246
-- title:
--   Claim 3.1 — telescoping: the dynamic program computes the utility (with p.8: the two OPT agree)
-- statement:
--   Run the dynamic program of Table 1 from the state $0$.
--
--   1. Along every sequence of actions and realizations, with final state $\alpha^{\mathrm{final}}$,
--   $$\sum_tg(I_t,a_t)=\sum_{j=1}^k\alpha_j^{\mathrm{final}}-\sum_{i:I_i=1}c_i.$$
--   2. Every policy of the dynamic program has an admissible model policy of the same expected utility.
--   3. Every admissible model policy is matched or beaten by a policy of the dynamic program.
--   4. The optimum of the dynamic program equals the Bellman value $\mathrm{OPT}(M,0,k)$ of §2.2.
--   5. This value is $\mathrm{OPT}(I)$ of §2.1: every admissible model policy has expected utility at most it, and some admissible model policy attains it, "so the two definitions agree".
--
--   This is the bridge between the model of §2.1, in which Theorem 1.1 is stated, and the dynamic program analyzed in §3.
--
--   Differences from the source:
--   - generalization: for any policy → along every sequence of actions and realizations, not only those of a policy; reason: a policy's execution is such a sequence
--   - encoding: a closed claim contributes vi to the utility → a closed claim enters E[vi] in the state, and the equalities with the utility are in expectation; reason: p.8: "its expected contribution to the utility is E[vi]"
--   - reading: "the expected total reward equals the expected utility", for any policy → equality from program policies to model policies; for the converse an inequality, with OPT equal; reason: the program always keeps the top k values, so a model policy that selects badly at its stop is strictly beaten by every program policy that follows it
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Claim 3.1, p.7 (PDF p.8), and p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_Inst_dp
import Definitions.Def_MultiSelectPandora_DPData_runTrace
import Definitions.Def_MultiSelectPandora_DPData_u
import Definitions.Def_MultiSelectPandora_DPAct
import Definitions.Def_MultiSelectPandora_DPPolicy
import Definitions.Def_MultiSelectPandora_Policy
import Definitions.Def_MultiSelectPandora_Admissible
import Definitions.Def_MultiSelectPandora_utility
import Definitions.Def_MultiSelectPandora_DPData_value
import Definitions.Def_MultiSelectPandora_OPT

namespace MultiSelectPandora

/-- **Claim 3.1 (telescoping)**, p.7 (PDF p.8), with the identification on p.8 (PDF p.9). Beyhaghi–Han–Luqman manuscript.

(a) Along every sequence of actions and realizations, the total reward is `Σ_j α^final_j − Σ_{i : I_i = 1} c_i`. (b) Every policy of the dynamic program has a
model policy of the same expected utility. (c) Every admissible model policy is matched or beaten by a policy of the dynamic program. (d) `OPT` of the dynamic
program is the Bellman value `optState` of §2.2, and (e) this value is `OPT(I)` of §2.1, the largest expected utility of an admissible
policy, attained by one, so the two definitions agree.

**Formalization Note.** Closed claims hold in expectation, not pathwise: the state receives `E[v_i]` (p.8). Part (c) is an inequality: the program always keeps the
top `k` values secured, so a model policy that selects badly at its stop is strictly beaten. -/
theorem claim_3_1 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) :
    (∀ tr : List (DPAct I.n × ℕ),
        (∀ e ∈ tr, ∀ i, e.1 = DPAct.openBox i → e.2 < I.s i) →
        (I.dp.runTrace tr (0 : Fin k → ℝ)).2 =
          ∑ j, (I.dp.runTrace tr (0 : Fin k → ℝ)).1 j -
            (tr.map fun e => match e.1 with
              | DPAct.openBox i => I.c i
              | _ => 0).sum) ∧
    (∀ π : DPPolicy I.n, ∃ π' : Policy I.n, Admissible I k π' ∧ I.dp.u k π = utility I k π') ∧
    (∀ π' : Policy I.n, Admissible I k π' → ∃ π : DPPolicy I.n, utility I k π' ≤ I.dp.u k π) ∧
    I.dp.value Finset.univ (0 : Fin k → ℝ) = OPT I k ∧
    (∀ π' : Policy I.n, Admissible I k π' → utility I k π' ≤ OPT I k) ∧
    ∃ π' : Policy I.n, Admissible I k π' ∧ utility I k π' = OPT I k := by sorry

end MultiSelectPandora
