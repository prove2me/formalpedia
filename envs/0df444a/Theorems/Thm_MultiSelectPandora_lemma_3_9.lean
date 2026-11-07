-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_9
-- name    : MultiSelectPandora.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:50.187825+00:00
-- url     : https://prove2.me/theorems/22e48bff-4ed2-4106-aa87-c4b5545c7d24
-- title:
--   Lemma 3.9 — above $\theta$, no closed claim is needed and Weitzman is optimal
-- statement:
--   Let $0<\varepsilon<1$, and let $\alpha$ be a state with $\alpha_k\ge\mathrm{OPT}/\varepsilon$, in particular any state with $\alpha_k\ge\theta$. For every set $U$ of boxes,
--   $$G_I(U,\alpha)+\sum_j\alpha_j=W(U,\alpha),$$
--   so an optimal continuation never claims a box closed, and the generalized Weitzman policy, under every tie-breaking, is an optimal continuation. That rule opens box $i$ only if $\sigma_i>\alpha_k$.
--
--   The large regime is therefore one of obligatory inspection, with the closed form of Fact 2.1.
--
--   Differences from the source:
--   - generalization: αk ≥ θ → OPT/ε ≤ αk; reason: θ ≥ OPT/ε by Lemma 3.8, so the source's hypothesis implies this one
--   - reading: ε unrestricted in the statement → ε < 1; reason: the proof's "for any ε < 1", p.30
--   - encoding: there is an optimal continuation that never claims a box closed → the equality with W, the optimal value without closed claims; reason: the two say the same
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.9, p.10 (PDF p.11); proof p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_Inst_dp
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_DPData_value
import Definitions.Def_MultiSelectPandora_W
import Definitions.Def_MultiSelectPandora_IsWeitzmanRule
import Definitions.Def_MultiSelectPandora_ruleValue

namespace MultiSelectPandora

/-- **Lemma 3.9 (optimal behavior in the large-value regime)**, p.10 (PDF p.11); proof p.30 (PDF p.31). Beyhaghi–Han–Luqman manuscript.

For a state with `α_k ≥ θ` there is an optimal continuation that never claims a box closed and opens box `i` only if `σ_i ≥ α_k`; in particular the generalized Weitzman policy is an optimal continuation.

**Formalization Note.** The hypothesis is `OPT/ε ≤ α_k`, which `θ ≤ α_k` implies since `θ ≥ OPT/ε`. `ε < 1` is the proof's ("for any `ε < 1`", p.30). Since `W` is the value without closed claims, `value + Σ α = W` says that none is needed. The rule opens box `i` only if `σ_i > α_k`, and it attains the value. -/
theorem lemma_3_9 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (U : Finset (Fin I.n)) (α : Fin k → ℝ) (hα : IsSortedState α) (hfl : OPT I k / ε ≤ stFloor α) :
    I.dp.value U α + ∑ j, α j = W I U α ∧
      ∀ rule, IsWeitzmanRule I k rule → ruleValue I rule U α = I.dp.value U α + ∑ j, α j := by sorry

end MultiSelectPandora
