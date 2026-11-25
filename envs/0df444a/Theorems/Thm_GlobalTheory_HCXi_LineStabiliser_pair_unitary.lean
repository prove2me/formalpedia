-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_LineStabiliser_pair_unitary
-- name    : GlobalTheory.HCXi.LineStabiliser.pair_unitary
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:58.815683+00:00
-- url     : https://prove2.me/theorems/a6ba3c51-d477-4eb8-b760-41aa7f7bb392
-- title:
--   Line Stabiliser: pair unitary
-- statement:
--   The Line Stabiliser construction uses the pair unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ParabolicLineStabilizerLevi.lean#L74-L76

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

theorem GlobalTheory.HCXi.LineStabiliser.pair_unitary {n : ℕ} (H p : Matrix (Fin n) (Fin n) ℂ) (hp : pᴴ * H * p = H) (v w : Fin n → ℂ) :
    star (p *ᵥ w) ⬝ᵥ (H *ᵥ (p *ᵥ v)) = star w ⬝ᵥ (H *ᵥ v) := by sorry
