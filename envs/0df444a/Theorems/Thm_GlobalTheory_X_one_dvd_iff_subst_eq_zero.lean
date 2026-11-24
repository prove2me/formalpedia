-- Prove2me | Theorems.Thm_GlobalTheory_X_one_dvd_iff_subst_eq_zero
-- name    : GlobalTheory.X_one_dvd_iff_subst_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:26.780312+00:00
-- url     : https://prove2.me/theorems/da6e8464-ff84-4958-99d4-5245a31e82e1
-- title:
--   Global Theory: X one dvd iff subst eq zero
-- statement:
--   The Global Theory construction uses the X one dvd iff subst eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L41-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SubstTwoVariablesIdentities.lean#L41-L67

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

theorem GlobalTheory.X_one_dvd_iff_subst_eq_zero {k : Type} [CommRing k] (g : MvPowerSeries (Fin 2) k) :
    X 1 ∣ g ↔ subst (![PowerSeries.X, 0] : Fin 2 → PowerSeries k) g = 0 := by sorry
