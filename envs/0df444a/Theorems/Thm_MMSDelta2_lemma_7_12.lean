-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_12
-- name    : MMSDelta2.lemma_7_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:08.807082+00:00
-- url     : https://prove2.me/theorems/657cf64c-030d-40d5-89d9-b06d5b201bf0
-- title:
--   Lemma 7.12 — in every MMS allocation $f$ gets $R_5$, $a^*$ gets $R_1$, $p$ gets $R_2$, $R_3$ or $R_4$
-- statement:
--   Let the source instance admit a solution. In every MMS allocation of the constructed instance, the anchor agent $f$ receives the last row $R_5$ of the core and the lex-opt indicator $a^*$ receives the first row $R_1$; consequently the puzzle-solving agent $p$ receives one of the rows $R_2,R_3,R_4$. Here "receives row $R_r$" means that the core goods of the agent's bundle are exactly $R_r$.
--
--   This pins down the core part of every MMS allocation.
--
--   **Formalization Note** Agents are numbered $0=p$, $1=a^*$, $2,3=q_1,q_2$, $4=f$; $\mathrm{MMS}_z$ is computed for the real-valued copy of the constructed instance.
--
--   Differences from the source:
--   - encoding: agents p, a*, q₁, q₂, f; MMS of the constructed instance → agents 0–4 of buildInstance; MMS_z = CutChoose.mu of its real copy; reason: fixed numbering; the values are integers
--   - encoding: the §7 standing promise: the source instance admits a solution → hypothesis I.HasSolution; reason: LexMax4Partition-Promise instances are promised to admit a solution, and OPT is defined only then
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.12, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_MMSDelta2_buildInstance
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2

/-- **Lemma 7.12**, p.35 (PDF p.37).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

In every MMS allocation, the anchor agent receives the last row `R_5`, and the lex-opt indicator
receives the first row `R_1`. Consequently, the puzzle-solving agent receives one of the other rows
`R_2, R_3, R_4`.

**Formalization Note.** Agents are `0 = p` (puzzle-solving), `1 = a*` (lex-opt indicator), `2, 3 = q_1, q_2`
(row-forcing), `4 = f` (anchor); rows are 0-based (`rowGoods 4` is `R_5`). Values are the real
copies `realVal I.buildInstance` of the integer values; `MMS_z` is `StrategicAlloc.CutChoose.mu`.
"Receives row `R_r`" is `A_z ∩ M_core = R_r`. The source instance has a solution (the promise). -/
theorem lemma_7_12 (I : FourPartInstance) (hI : I.HasSolution)
    (A : Fin 5 → Finset (Fin (numCore + 4 * I.q * I.q)))
    (hA : StrategicAlloc.RRFair.IsAllocation A)
    (hMMS : StrategicAlloc.CutChoose.IsApproxMMS 1 (realVal I.buildInstance) A) :
    A 4 ∩ I.coreGoods = I.rowGoods 4 ∧ A 1 ∩ I.coreGoods = I.rowGoods 0 ∧
      (A 0 ∩ I.coreGoods = I.rowGoods 1 ∨ A 0 ∩ I.coreGoods = I.rowGoods 2 ∨
        A 0 ∩ I.coreGoods = I.rowGoods 3) := by sorry

end MMSDelta2
