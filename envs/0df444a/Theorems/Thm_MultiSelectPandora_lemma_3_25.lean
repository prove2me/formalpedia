-- Prove2me | Theorems.Thm_MultiSelectPandora_lemma_3_25
-- name    : MultiSelectPandora.lemma_3_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:25.850754+00:00
-- url     : https://prove2.me/theorems/1e1e8eab-655a-4916-9b18-901343308823
-- title:
--   Lemma 3.25 — small-value discretization, in both directions
-- statement:
--   Let $I$ be a valid instance with $0<\mathrm{OPT}$, $k\ge1$ and $\varepsilon>0$.
--
--   1. For any policy $\pi$ there is an S-discretized policy $\pi_S$ with
--   $$u(\pi_S,I^S)\ge u(\pi,I)-k\theta\varepsilon^2,$$
--   and $k\theta\varepsilon^2\le2k\varepsilon\,\mathrm{OPT}$, which is the bound $O(k\varepsilon)\mathrm{OPT}$.
--   2. Conversely, for any S-discretized policy $\pi_S$, $u(\pi_S,I)\ge u(\pi_S,I^S)$.
--
--   This is the first step of the discretization.
--
--   Differences from the source:
--   - reading: O(kε)·OPT → kθε², with kθε² ≤ 2kε·OPT as a clause; reason: the value in the proof, p.33
--   - generalization: πS may be randomized (the paper's simulation) → πS deterministic; reason: the simulation is a mixture of deterministic S-discretized policies, each picking one representative per box and level, so one of them does as well
--   - encoding: any policy π on I → any deterministic policy of the dynamic program; reason: a randomized policy is a mixture of them, and claim_3_1 relates them to the model
--   - encoding: no hypothesis on OPT → 0 < OPT; reason: θ = OPT^/ε is 0 when OPT = 0 and p.14 divides by it, so this excludes only an undefined case
--   - reading: σi "the solution" of E[(vi − σi)+] = ci → the least solution; reason: the solution is not unique when ci = 0; κi is the same for every choice
--   - encoding: a law Fi with finite support → explicit support positions with values and probabilities, and expectations as finite sums with independence by product form; reason: p.5: "Each Fi is given explicitly, with finite support"
--   - encoding: "every constant k"; the searcher selects k prizes → k ≥ 1; reason: at k = 0 nothing can be selected, and the state has no floor
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), Lemma 3.25, p.16 (PDF p.17); proof pp.32–33 (PDF pp.33–34)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_Valid
import Definitions.Def_MultiSelectPandora_Inst_dp
import Definitions.Def_MultiSelectPandora_OPT
import Definitions.Def_MultiSelectPandora_theta
import Definitions.Def_MultiSelectPandora_IS
import Definitions.Def_MultiSelectPandora_IsSDiscretized
import Definitions.Def_MultiSelectPandora_DPData_u
import Definitions.Def_MultiSelectPandora_DPPolicy

namespace MultiSelectPandora

/-- **Lemma 3.25 (small-value discretization)**, p.16 (PDF p.17); proof pp.32–33 (PDF pp.33–34). Beyhaghi–Han–Luqman manuscript.

**Formalization Note.** `O(kε) OPT` is written out as in the proof: the loss is `kθε²`, and `kθε² ≤ 2kε OPT` is the second clause. `0 < OPT` excludes the undefined `θ = 0`. The policy `πS` is deterministic: the paper's simulation is a mixture of deterministic S-discretized policies, each picking one representative per box and level, so one of them does as well. -/
theorem lemma_3_25 (I : Inst) (hI : I.Valid) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hOPT : 0 < OPT I k) :
    (∀ π : DPPolicy I.n, ∃ πS : DPPolicy I.n, IsSDiscretized I k ε πS ∧
        I.dp.u k π - k * theta I k ε * ε ^ 2 ≤ (IS I k ε).u k πS) ∧
      k * theta I k ε * ε ^ 2 ≤ 2 * k * ε * OPT I k ∧
      ∀ πS : DPPolicy I.n, IsSDiscretized I k ε πS → (IS I k ε).u k πS ≤ I.dp.u k πS := by sorry

end MultiSelectPandora
