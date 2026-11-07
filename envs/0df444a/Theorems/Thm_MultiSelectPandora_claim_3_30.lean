-- Prove2me | Theorems.Thm_MultiSelectPandora_claim_3_30
-- name    : MultiSelectPandora.claim_3_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:00.529465+00:00
-- url     : https://prove2.me/theorems/050ca3c8-e2d2-4c1a-b22c-1ef1c058c136
-- title:
--   Claim 3.30 — a policy for $I^{SL}$ does at least as well on $I$
-- statement:
--   For a valid instance with $0<\mathrm{OPT}$, $k\ge1$, $\varepsilon>0$ and every policy $\pi$ of the dynamic program,
--   $$u(\pi,I)\ge u(\pi,I^{SL}),$$
--   where the same function of the history is executed on $I$.
--
--   So the near-optimal policy for $I^{SL}$ given by Fact 3.3 can be carried back to the original instance.
--
--   Differences from the source:
--   - generalization: a policy for ISL, which reads w only → every function of the history of actions and positions; reason: the positions are shared, and a policy reading only w is one such function
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: ⊤ is "an arbitrary fixed number greater than MaxV" (footnote 2) → ⊤ is a number above MaxV and above every value of the instance; reason: Remark A.4 and Claim A.7 need D^L(v) ≥ v for every v; with ⊤ = MaxV + 1 Claim 3.30 fails (two boxes, value 1000 with probability 0.1, else 0, c = 90, k = 1, ε = 1/4; gap 5.23)
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Claim 3.30, p.17 (PDF p.18); proof p.17 and Claim A.7, pp.35–36 (PDF pp.36–37)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_Inst_dp
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_ISL
import Definitions.Def_MultiSelectPandora_DPData_u
import Definitions.Def_MultiSelectPandora_DPPolicy

namespace MultiSelectPandora

/-- **Claim 3.30 (execution on the original instance)**, p.17 (PDF p.18); proof p.17 and Claim A.7, pp.35–36 (PDF pp.36–37). Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** The same function of the history is executed on `I`. The positions are shared, so the statement is for every policy, not only those reading `w`, which is all `I^SL` can reveal. `⊤` is above every value (`topLevel`), which this claim needs. -/
theorem claim_3_30 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hOPT : 0 < OPT I k)
    (π : DPPolicy I.n) : (ISL I k ε).u k π ≤ I.dp.u k π := by sorry

end MultiSelectPandora
