-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_7
-- name    : MultiSelectPandora.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:15:44.388825+00:00
-- url     : https://prove2.me/theorems/1b1731da-5d12-49eb-a7d9-d24806ad4fab
-- title:
--   Lemma 3.7 — Condition (C4): $\mathrm{MAX}=\mathrm{OPT}$
-- statement:
--   For a valid instance, $k\ge1$ and every state $\alpha$,
--   $$G_I(M,\alpha)\le G_I(M,0).$$
--   Since $0$ is a state, this says $\mathrm{MAX}=\mathrm{OPT}$ for the program of Table 1, which is Condition (C4). A lower starting state can only help, as the marginal reward is non-increasing in the state.
--
--   Differences from the source:
--   - encoding: MAX = OPT → the inequality at every state, with MAX not defined as a number on the infinite state set; reason: 0 is a state, so the two are equivalent
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.7, p.9 (PDF p.10); proof pp.28–29 (PDF pp.29–30)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_Inst_dp
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_DPData_value

namespace MultiSelectPandora

/-- **Lemma 3.7 (Condition (C4))**, p.9 (PDF p.10); proof pp.28–29 (PDF pp.29–30). Beyhaghi–Han–Luqman manuscript.

`MAX = OPT`: from every state `α`, the optimal total reward is at most the one from `0`.

**Formalization Note.** `0` is a state, so this inequality is exactly `MAX = OPT` over the (infinite) state set of Table 1. -/
theorem lemma_3_7 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (α : Fin k → ℝ) (hα : IsSortedState α) :
    I.dp.value Finset.univ α ≤ I.dp.value Finset.univ (0 : Fin k → ℝ) := by sorry

end MultiSelectPandora
