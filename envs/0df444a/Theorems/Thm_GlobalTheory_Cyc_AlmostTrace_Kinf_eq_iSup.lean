-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Kinf_eq_iSup
-- name    : GlobalTheory.Cyc.AlmostTrace.Kinf_eq_iSup
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:32:31.221029+00:00
-- url     : https://prove2.me/theorems/5121e62e-27af-4572-ba0d-d55c66d16a98
-- title:
--   Almost Trace: Kinf eq i Sup
-- statement:
--   The Almost Trace construction uses the Kinf eq i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L27-L40

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

theorem GlobalTheory.Cyc.AlmostTrace.Kinf_eq_iSup (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by sorry
