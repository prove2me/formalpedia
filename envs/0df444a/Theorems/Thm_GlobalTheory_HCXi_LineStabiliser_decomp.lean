-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_decomp
-- name    : GlobalTheory.HCXi.LineStabiliser.decomp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:28.601797+00:00
-- url     : https://prove2.me/theorems/f522893e-5332-5e92-9ecf-61adcee6ada4
-- title:
--   Line Stabiliser: decomp
-- statement:
--   The Line Stabiliser construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L53-L72

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

theorem GlobalTheory.HCXi.LineStabiliser.decomp (u : Fin (2 * (1 + r') + k + 1) → ℂ) (hu : u (lst k r') = 0) :
    u = liftVec k 1 r' ((incl k 1 r')ᴴ *ᵥ u) + u (fst k r') • e0 k r' := by sorry
