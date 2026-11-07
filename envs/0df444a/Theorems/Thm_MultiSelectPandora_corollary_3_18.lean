-- Prove2me | Theorems.Thm_MultiSelectPandora_corollary_3_18
-- name    : MultiSelectPandora.corollary_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:11:32.058446+00:00
-- url     : https://prove2.me/theorems/3f06e73a-6c41-4ca5-af6d-1765603099de
-- title:
--   Corollary 3.18 — above $\theta$, $\Phi(M,\alpha)\le(1+O(\varepsilon))\mathrm{OPT}$
-- statement:
--   For $0<\varepsilon\le1/4$ and a state with $\alpha_k\ge\mathrm{OPT}/\varepsilon$, in particular any state with $\alpha_k\ge\theta$,
--   $$\Phi(M,\alpha)\le(1+4\varepsilon)\,\mathrm{OPT}.$$
--   In particular $\Phi(M,\alpha)\le2\,\mathrm{OPT}=O(\mathrm{OPT})$. This bounds the number of grid points.
--
--   Differences from the source:
--   - reading: (1 + O(ε)) OPT "for sufficiently small ε" → (1 + 4ε) OPT for ε ≤ 1/4; reason: the value in the proof: (1 − 2ε)Φ ≤ G^W ≤ OPT and 1/(1 − 2ε) ≤ 1 + 4ε on this range
--   - generalization: αk ≥ θ → OPT/ε ≤ αk; reason: θ ≥ OPT/ε by Lemma 3.8, so the source's hypothesis implies this one
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Corollary 3.18, p.14 (PDF p.15); proof p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_IsSortedState
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_Phi

namespace MultiSelectPandora

/-- **Corollary 3.18**, p.14 (PDF p.15); proof p.30 (PDF p.31). Beyhaghi–Han–Luqman manuscript.

For a state with `α_k ≥ θ`: `Φ(M, α) ≤ (1 + O(ε)) OPT` for small `ε`, hence `Φ(M, α) ≤ O(OPT)`.

**Formalization Note.** The constant comes from `(1 − 2ε) Φ ≤ G^W ≤ OPT`, with `1/(1 − 2ε) ≤ 1 + 4ε` on `ε ≤ 1/4`. In particular `Φ ≤ 2 OPT` there. -/
theorem corollary_3_18 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4)
    (α : Fin k → ℝ) (hα : IsSortedState α) (hfl : OPT I k / ε ≤ stFloor α) :
    Phi I Finset.univ (stFloor α) ≤ (1 + 4 * ε) * OPT I k := by sorry

end MultiSelectPandora
