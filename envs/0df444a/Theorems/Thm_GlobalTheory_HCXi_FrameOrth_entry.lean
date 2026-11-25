-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_FrameOrth_entry
-- name    : GlobalTheory.HCXi.FrameOrth.entry
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:50:33.783817+00:00
-- url     : https://prove2.me/theorems/b2cf97e9-94d6-4820-805a-3659d96fe250
-- title:
--   Frame Orth: entry
-- statement:
--   The Frame Orth construction uses the entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/FrameIsotropicOrthonormal.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormal
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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.FrameOrth

theorem GlobalTheory.HCXi.FrameOrth.entry (k r : ℕ) (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Fin (r + 1)) :
    ((frame k r)ᴴ * M * frame k r) a b =
      star (fvec k r (isoVec k r) a) ⬝ᵥ (M *ᵥ fvec k r (isoVec k r) b) := by sorry
