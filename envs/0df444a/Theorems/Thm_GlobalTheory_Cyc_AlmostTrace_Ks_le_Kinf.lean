-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf
-- name    : GlobalTheory.Cyc.AlmostTrace.Ks_le_Kinf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:26.089924+00:00
-- url     : https://prove2.me/theorems/a36fe572-806d-40c6-bef9-0bf0e2b22bb4
-- title:
--   Almost Trace: Ks le Kinf
-- statement:
--   The Almost Trace construction uses the Ks le Kinf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TraceAlmostOntoOfLevels.lean#L13-L16

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

theorem GlobalTheory.Cyc.AlmostTrace.Ks_le_Kinf (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by sorry
