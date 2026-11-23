-- Prove2me | Theorems.Thm_GlobalTheory_DerivAtOrigin_count_cons_eq
-- name    : GlobalTheory.DerivAtOrigin.count_cons_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:38.135718+00:00
-- url     : https://prove2.me/theorems/5f56eafd-b18b-446d-8c55-e691acc96dd4
-- title:
--   Deriv At Origin: count cons eq
-- statement:
--   The Deriv At Origin construction uses the count cons eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L16-L21

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

theorem GlobalTheory.DerivAtOrigin.count_cons_eq {I : Type} [DecidableEq I] (i : I) (l : List I) :
    (fun j => (i :: l).count j) = (fun j => l.count j) + Pi.single i 1 := by sorry
