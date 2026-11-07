-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_16
-- name    : MultiSelectPandora.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:29.340245+00:00
-- url     : https://prove2.me/theorems/e867d9c6-ed30-4831-8946-098e46f8c414
-- title:
--   Lemma 3.16 — $G^W\ge(1-O(\varepsilon))\Phi$, the paper's main lemma
-- statement:
--   Let $\varepsilon>0$, $k\ge1$, and let $\alpha$ be a state with $\alpha_k\ge\mathrm{OPT}/\varepsilon$, in particular any state with $\alpha_k\ge\theta$. For every set $U$ of boxes,
--   $$G^W(U,\alpha)\ge\Big(1-\big(1+\tfrac1k\big)\varepsilon\Big)\Phi(U,\alpha).$$
--
--   So the additive proxy $\Phi$ controls the continuation gain from below, with a constant that does not grow with $k$. This is what makes the rounding of large values affordable.
--
--   Differences from the source:
--   - reading: 1 − O(ε) → 1 − (1 + 1/k)ε; reason: the value in the proof, p.14: Φ − G^W ≤ (ε/k + ε)Φ
--   - generalization: αk ≥ θ → OPT/ε ≤ αk; reason: θ ≥ OPT/ε by Lemma 3.8, so the source's hypothesis implies this one
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.16, p.11 (PDF p.12); proof pp.11–14 (PDF pp.12–15)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_Phi
import Definitions.Def_MultiSelectPandora_GW

namespace MultiSelectPandora

/-- **Lemma 3.16 (lower bound `G^W ≥ (1 − O(ε)) Φ`)**, p.11 (PDF p.12); proof pp.11–14 (PDF pp.12–15). Beyhaghi–Han–Luqman manuscript. The paper's main lemma.

**Formalization Note.** The constant is the proof's: `Φ − G^W ≤ (ε/k + ε) Φ` (p.14), which does not grow with `k`. The hypothesis is `OPT/ε ≤ α_k`, implied by `α_k ≥ θ`. -/
theorem lemma_3_16 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (U : Finset (Fin I.n))
    (α : Fin k → ℝ) (hα : IsSortedState α) (hfl : OPT I k / ε ≤ stFloor α) :
    (1 - (1 + 1 / (k : ℝ)) * ε) * Phi I U (stFloor α) ≤ GW I U α := by sorry

end MultiSelectPandora
