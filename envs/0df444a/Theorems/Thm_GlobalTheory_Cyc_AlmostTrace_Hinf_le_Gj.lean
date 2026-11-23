-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Hinf_le_Gj
-- name    : GlobalTheory.Cyc.AlmostTrace.Hinf_le_Gj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:29:02.146119+00:00
-- url     : https://prove2.me/theorems/0ff345a8-88b1-4185-b418-eea03b6e38a7
-- title:
--   Almost Trace: Hinf le Gj
-- statement:
--   The Almost Trace construction uses the Hinf le Gj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L48-L50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.AlmostTrace.Hinf_le_Gj (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by sorry
