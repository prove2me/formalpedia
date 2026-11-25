-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_shift
-- name    : GlobalTheory.HCXi.LineStabiliser.pair_shift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:12.658055+00:00
-- url     : https://prove2.me/theorems/10bf6af8-8e23-589c-8918-6650fe840f5b
-- title:
--   Line Stabiliser: pair shift
-- statement:
--   The Line Stabiliser construction uses the pair shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L82-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L82-L87

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

theorem GlobalTheory.HCXi.LineStabiliser.pair_shift (v w : Fin (2 * r' + k + 1) → ℂ) (c d : ℂ) :
    star (liftVec k 1 r' w + d • e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ (liftVec k 1 r' v + c • e0 k r')) =
      star w ⬝ᵥ (Hpk k r' *ᵥ v) := by sorry
