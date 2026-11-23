-- Prove2me | Theorems.Thm_GlobalTheory_DerivAtOrigin_zero_mem_polydisc
-- name    : GlobalTheory.DerivAtOrigin.zero_mem_polydisc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:28.669128+00:00
-- url     : https://prove2.me/theorems/c3d508ff-141c-4c4d-9706-2852c3e3616f
-- title:
--   Deriv At Origin: zero mem polydisc
-- statement:
--   The Deriv At Origin construction uses the zero mem polydisc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L13-L14

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

theorem GlobalTheory.DerivAtOrigin.zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := by sorry
