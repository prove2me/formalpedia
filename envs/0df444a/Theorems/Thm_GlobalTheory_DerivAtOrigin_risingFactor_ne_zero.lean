-- Prove2me | Theorems.Thm_GlobalTheory_DerivAtOrigin_risingFactor_ne_zero
-- name    : GlobalTheory.DerivAtOrigin.risingFactor_ne_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:43:41.850931+00:00
-- url     : https://prove2.me/theorems/4ceee2ff-13e6-47de-9703-6955e1984b20
-- title:
--   Deriv At Origin: rising Factor ne zero
-- statement:
--   The Deriv At Origin construction uses the rising Factor ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivFormulaOfSeries.lean#L23-L33

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

theorem GlobalTheory.DerivAtOrigin.risingFactor_ne_zero {I : Type} [Fintype I] (k : ℕ) (hk : 1 ≤ k) (κ : I → ℕ) :
    risingFactor k κ ≠ 0 := by sorry
