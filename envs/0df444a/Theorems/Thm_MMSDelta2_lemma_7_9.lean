-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_9
-- name    : MMSDelta2.lemma_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:02:41.82878+00:00
-- url     : https://prove2.me/theorems/2a8d9ed0-d394-449a-93e7-c3fb70983eea
-- title:
--   Lemma 7.9 — $\mathrm{MMS}_p=\mathrm{MMS}_{q_1}=\mathrm{MMS}_{q_2}=\mathrm{MMS}_f=\tau$
-- statement:
--   In the five-agent instance constructed from any 4-PARTITION instance:
--
--   1. the puzzle-solving agent $p$ has $\mathrm{MMS}_p=\tau$;
--   2. every row-forcing agent $q\in\{q_1,q_2\}$ has $\mathrm{MMS}_q=\tau$;
--   3. the anchor agent $f$ has $\mathrm{MMS}_f=\tau$,
--
--   where $\tau=\Gamma\alpha$.
--
--   These maximin shares are the thresholds every MMS allocation must meet.
--
--   **Formalization Note** Agents are numbered $0=p$, $1=a^*$, $2,3=q_1,q_2$, $4=f$; $\mathrm{MMS}_z$ is computed for the real-valued copy of the constructed instance.
--
--   Differences from the source:
--   - encoding: agents p, a*, q₁, q₂, f; MMS of the constructed instance → agents 0–4 of buildInstance; MMS_z = CutChoose.mu of its real copy; reason: fixed numbering; the values are integers
--   - generalization: the §7 standing assumption: (W, T) is a LexMax4Partition-Promise instance, promised to admit a solution (p.27) → no promise: the statement holds for every 4-PARTITION instance I; reason: the proof (p.33) uses only Observations 7.4, 7.6, 7.7 and averaging, never a solution; promise instances are a special case
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.9, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_MMSDelta2_buildInstance
import Definitions.Def_MMSDelta2_HasMMSAllocation

namespace MMSDelta2

/-- **Lemma 7.9**, p.32 (PDF p.34).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

In the constructed instance: (1) `MMS_p = τ` for the puzzle-solving agent `p`; (2) `MMS_q = τ` for
every row-forcing agent `q`; (3) `MMS_f = τ` for the anchor agent `f`.

**Formalization Note.** Agents are `0 = p` (puzzle-solving), `1 = a*` (lex-opt indicator), `2, 3 = q_1, q_2`
(row-forcing), `4 = f` (anchor); rows are 0-based (`rowGoods 4` is `R_5`). Values are the real
copies `realVal I.buildInstance` of the integer values; `MMS_z` is `StrategicAlloc.CutChoose.mu`.
The statement holds for every 4-PARTITION instance (no promise is used). -/
theorem lemma_7_9 (I : FourPartInstance) :
    StrategicAlloc.CutChoose.mu (realVal I.buildInstance) 0 = (I.tau : ℝ) ∧
    StrategicAlloc.CutChoose.mu (realVal I.buildInstance) 2 = (I.tau : ℝ) ∧
    StrategicAlloc.CutChoose.mu (realVal I.buildInstance) 3 = (I.tau : ℝ) ∧
    StrategicAlloc.CutChoose.mu (realVal I.buildInstance) 4 = (I.tau : ℝ) := by sorry

end MMSDelta2
