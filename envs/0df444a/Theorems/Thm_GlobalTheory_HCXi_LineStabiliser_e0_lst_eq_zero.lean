-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_e0_lst_eq_zero
-- name    : GlobalTheory.HCXi.LineStabiliser.e0_lst_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:19:21.426568+00:00
-- url     : https://prove2.me/theorems/2e01ba27-8fa6-498b-a538-a5c0160156df
-- title:
--   Line Stabiliser: e0 lst eq zero
-- statement:
--   The Line Stabiliser construction uses the e0 lst eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L48-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LevMulVecOutside
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.LineStabiliser
open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser
variable (k r' : ℕ)

theorem GlobalTheory.HCXi.LineStabiliser.e0_lst_eq_zero : e0 k r' (lst k r') = 0 := by sorry
