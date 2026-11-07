-- Prove2me | Theorems.Thm_MultiSelectPandora_fact_2_1
-- name    : MultiSelectPandora.fact_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:16:39.356727+00:00
-- url     : https://prove2.me/theorems/48fa2ea5-d094-4110-93cd-3f3e81af3d06
-- title:
--   Fact 2.1 — the generalized Weitzman policy is optimal, $W(U,\alpha)=E[\sum_j\beta_j]$
-- statement:
--   Fix an instance, $k\ge1$, a set $U$ of boxes and a state $\alpha$ of outside options. With obligatory inspection, the optimal expected utility of $P(U,\alpha,0)$ is
--   $$W(U,\alpha)=E\Big[\sum_{j=1}^k\beta_j\Big],\qquad\beta=\mathrm{top}_k\big(\alpha\cup\{\kappa_i\}_{i\in U}\big),$$
--   and the generalized Weitzman policy attains it, under every tie-breaking.
--
--   Thus the optimal utility equals the expected sum of the $k$ largest capped and observed values, as if the capped values were observed at no cost. This closed form gives the estimate of $\mathrm{OPT}$ and the analysis of the fully large regime.
--
--   Differences from the source:
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: the generalized Weitzman policy on (U, α) → a rule on sets of unopened boxes and states, whose expected utility is computed by recursion; reason: the policy of p.6 reads only the unopened boxes and the state
--   - reading: the policy's tie-breaking is unspecified → every tie-breaking that is a function of (U, α); reason: ties are the only freedom of the rule, and the rule has this form
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Fact 2.1 ([Sin18, Theorem 1.2]; see also [KWW16]), p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_W
import Definitions.Def_MultiSelectPandora_cappedTop
import Definitions.Def_MultiSelectPandora_IsWeitzmanRule
import Definitions.Def_MultiSelectPandora_ruleValue

namespace MultiSelectPandora

/-- **Fact 2.1 (generalized Weitzman)**, p.6 (PDF p.7). Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS
and a Structural Separation*, manuscript (STOC 2027 submission), citing [Sin18, Theorem 1.2] and [KWW16].

`W(U, α) = E[Σ_j β_j]` with `β = top_k(α ∪ {κ_i}_{i ∈ U})`, and the generalized Weitzman rule, under every tie-breaking, attains `W(U, α)`.

**Formalization Note.** `α` is any state (the outside options) and `U` any set of boxes. `σ_i` is the least solution, so zero costs are covered. -/
theorem fact_2_1 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (U : Finset (Fin I.n)) (α : Fin k → ℝ)
    (hα : IsSortedState α) :
    W I U α = cappedTop I U α ∧
      ∀ rule, IsWeitzmanRule I k rule → ruleValue I rule U α = W I U α := by sorry

end MultiSelectPandora
