-- Prove2me | Theorems.Thm_GlobalTheory_DerivAtOrigin_isOpen_polydisc
-- name    : GlobalTheory.DerivAtOrigin.isOpen_polydisc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:32.530731+00:00
-- url     : https://prove2.me/theorems/0d323253-a556-46cf-8106-3a09dc485882
-- title:
--   Deriv At Origin: is Open polydisc
-- statement:
--   The Deriv At Origin construction uses the is Open polydisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivFormulaOfSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DerivAtOrigin

theorem GlobalTheory.DerivAtOrigin.isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by sorry
