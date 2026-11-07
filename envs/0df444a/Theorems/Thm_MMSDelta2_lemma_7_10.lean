-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_10
-- name    : MMSDelta2.lemma_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:10.442281+00:00
-- url     : https://prove2.me/theorems/fc103cef-d8d2-4c86-ba01-c89805c6808a
-- title:
--   Lemma 7.10 — $\mathrm{MMS}_{a^*}=\tau+\mathrm{OPT}$
-- statement:
--   Let the 4-PARTITION source instance admit a solution, and let $\mathrm{OPT}$ be the maximum score of a solution. In the constructed five-agent instance the lex-opt indicator $a^*$ has
--
--   $$\mathrm{MMS}_{a^*}=\tau+\mathrm{OPT}.$$
--
--   Thus the maximin share of $a^*$ encodes the optimum of the source problem, which the reduction never computes.
--
--   **Formalization Note** Agents are numbered $0=p$, $1=a^*$, $2,3=q_1,q_2$, $4=f$; $\mathrm{MMS}_z$ is computed for the real-valued copy of the constructed instance.
--
--   Differences from the source:
--   - encoding: agents p, a*, q₁, q₂, f; MMS of the constructed instance → agents 0–4 of buildInstance; MMS_z = CutChoose.mu of its real copy; reason: fixed numbering; the values are integers
--   - encoding: the §7 standing promise: the source instance admits a solution → hypothesis I.HasSolution; reason: LexMax4Partition-Promise instances are promised to admit a solution, and OPT is defined only then
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.10, p.33 (PDF p.35); Claims 7.10.1–7.10.2, pp.33–34

import Mathlib
import Definitions.Def_MMSDelta2_buildInstance
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2

/-- **Lemma 7.10**, p.33 (PDF p.35); Claims 7.10.1 and 7.10.2, pp.33–34.

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

For the lex-opt indicator, `MMS_{a*} = τ + OPT`.

**Formalization Note.** Agents are `0 = p` (puzzle-solving), `1 = a*` (lex-opt indicator), `2, 3 = q_1, q_2`
(row-forcing), `4 = f` (anchor); rows are 0-based (`rowGoods 4` is `R_5`). Values are the real
copies `realVal I.buildInstance` of the integer values; `MMS_z` is `StrategicAlloc.CutChoose.mu`.
The source instance is a LexMax4Partition-Promise instance, so it has a solution and `OPT` is the
maximum score of a solution. -/
theorem lemma_7_10 (I : FourPartInstance) (hI : I.HasSolution) :
    StrategicAlloc.CutChoose.mu (realVal I.buildInstance) 1 = (I.tau : ℝ) + (I.OPT : ℝ) := by sorry

end MMSDelta2
