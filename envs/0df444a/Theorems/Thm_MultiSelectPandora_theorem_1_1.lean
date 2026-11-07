-- Prove2me | Theorems.Thm_MultiSelectPandora_theorem_1_1
-- name    : MultiSelectPandora.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:54.542518+00:00
-- url     : https://prove2.me/theorems/974e0776-857c-4d29-a0d4-d53d8adcdc0a
-- title:
--   Theorem 1.1 — a PTAS for k-PNOI
-- statement:
--   For every constant $k\ge1$ and every fixed $\varepsilon>0$ there is a polynomial-time algorithm that, given a valid rational instance of k-PNOI and a history, computes the next action of an admissible policy $\pi$ with
--   $$u(\pi,I)\ge(1-\varepsilon)\,\mathrm{OPT}(I).$$
--
--   There are $n$ boxes; box $i$ costs $c_i\ge0$ to open and holds an independent value $v_i\ge0$ of explicitly given finite-support law. The searcher opens boxes adaptively, then selects up to $k$ of them, each opened (worth $v_i$) or unopened (worth $E[v_i]$ in expectation). The utility is the selected value minus the costs paid. $\mathrm{OPT}$ is the largest expected utility of a policy. No polynomial-time approximation scheme was known for $k\ge2$, and the problem is NP-hard already for $k=1$.
--
--   **Formalization Note** The polynomial may depend on $k$ and $\varepsilon$: it is a PTAS and not an EPTAS. The bound is stated against every admissible policy of nonnegative utility, which is equivalent to $(1-\varepsilon)\mathrm{OPT}$, since $\mathrm{OPT}\ge0$ is attained. There is no hypothesis on $\mathrm{OPT}$, and no bound on $\varepsilon$, $k$, $n$ or the supports.
--
--   Differences from the source:
--   - reading: "polynomial in the input size, that is, in n and the total support size s", in no fixed arithmetic model → Turing.TM2ComputableInPolyTime, polynomial in the binary length of a rational input; reason: the paper fixes no model; a unit-cost model with floor is too strong to mean anything, and a cost monad would need the [FLX18a] program, which this paper does not contain
--   - reading: "computes a policy" → a machine computing the next action from (instance, history); reason: an explicit decision tree can have exponential size, so a policy is computed implicitly, as the [FLX18a] block-adaptive tree is; a free policy code with a free decoder would be trivial
--   - encoding: Fi given explicitly, values and costs real → rational data for the machine; reason: a Turing machine reads finite words, and "given explicitly" has no other meaning for one
--   - encoding: (1 − ε) OPT, with OPT the largest utility of a policy → (1 − ε) u(π') ≤ u(π) for every admissible π' with u(π') ≥ 0; reason: OPT ≥ 0 is attained, as stop ∅ has utility 0; for ε > 1 a competitor of negative utility would flip the inequality, which (1 − ε) OPT does not
--   - encoding: the competitor may be randomized → deterministic competitors π', with support positions in histories; reason: a randomized policy is a mixture of deterministic ones and cannot beat the best of them
--   - encoding: a closed claim is worth vi, unobserved → E[vi]; reason: p.5: "it contributes E[vi] in expectation"
--   - generalization: the computed policy may be randomized → the computed policy is deterministic; reason: a deterministic policy is a special randomized one
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Theorem 1.1, p.2 (PDF p.3); restated p.6 (PDF p.7); proof p.17 (PDF p.18)

import Mathlib
import Definitions.Def_MultiSelectPandora_RawInst
import Definitions.Def_MultiSelectPandora_RawInst_Valid
import Definitions.Def_MultiSelectPandora_RawInst_toInst
import Definitions.Def_MultiSelectPandora_RawAct
import Definitions.Def_MultiSelectPandora_Policy
import Definitions.Def_MultiSelectPandora_Admissible
import Definitions.Def_MultiSelectPandora_utility
import Definitions.Def_MultiSelectPandora_policyOf
import Definitions.Def_MultiSelectPandora_encIn
import Definitions.Def_MultiSelectPandora_encAct

namespace MultiSelectPandora

/-- **Theorem 1.1 (PTAS for k-PNOI)**, p.2 (PDF p.3); restated p.6 (PDF p.7); proof p.17 (PDF p.18). Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a
Structural Separation*, manuscript (STOC 2027 submission): "For every fixed `ε > 0` and every constant `k`, there is an algorithm that runs in time polynomial in the input size and computes a policy for k-PNOI with expected
utility at least `(1 − ε) OPT`."

**Formalization Note.** `k` and `ε` are fixed before the machine, so the polynomial may depend on them. "Polynomial time" is Mathlib's `Turing.TM2ComputableInPolyTime` on binary rational instances and histories, and "computes a policy" is a machine for the next action on (instance, history). The comparison is with every admissible policy of nonnegative utility, which says "`(1 − ε) OPT`" without a supremum: `OPT ≥ 0` since `stop ∅` has utility `0`, and for `ε > 1` a competitor of negative utility would flip the inequality, which `(1 − ε) OPT` does not. There is no hypothesis `0 < OPT` and no bound on `ε`, `k`, `n` or the supports. -/
theorem theorem_1_1 :
    ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ next : RawInst × List (ℕ × ℕ) → RawAct,
        Nonempty (Turing.TM2ComputableInPolyTime encIn encAct next) ∧
        ∀ I : RawInst, I.Valid →
          Admissible I.toInst k (policyOf next I) ∧
            ∀ π' : Policy I.toInst.n, Admissible I.toInst k π' → 0 ≤ utility I.toInst k π' →
              (1 - ε) * utility I.toInst k π' ≤ utility I.toInst k (policyOf next I) := by sorry

end MultiSelectPandora
