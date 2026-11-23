-- Prove2me | Theorems.Thm_GlobalTheory_hasSubst_pair
-- name    : GlobalTheory.hasSubst_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:45:35.468967+00:00
-- url     : https://prove2.me/theorems/4fb25efe-7c2a-46b7-9a3a-b840a23dd583
-- title:
--   Global Theory: has Subst pair
-- statement:
--   The Global Theory construction uses the has Subst pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SubstTwoVariablesIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPowerSeries

theorem GlobalTheory.hasSubst_pair {τ k : Type} [CommRing k] {z w : MvPowerSeries τ k}
    (hz : constantCoeff z = 0) (hw : constantCoeff w = 0) :
    HasSubst (![z, w] : Fin 2 → MvPowerSeries τ k) := by sorry
