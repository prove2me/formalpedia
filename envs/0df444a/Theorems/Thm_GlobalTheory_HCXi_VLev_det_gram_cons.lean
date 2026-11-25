-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_VLev_det_gram_cons
-- name    : GlobalTheory.HCXi.VLev.det_gram_cons
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:12:56.890747+00:00
-- url     : https://prove2.me/theorems/4ea2de32-9128-4a49-b273-632ee41eeebe
-- title:
--   VLev: det gram cons
-- statement:
--   The VLev construction uses the det gram cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L14-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L14-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_LevelGroupUnitaryHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ParabolicLineStabilizerLeviStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_KsetTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeLeviRecursion
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
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.VLev

theorem GlobalTheory.HCXi.VLev.det_gram_cons {n m : ℕ} (e : Fin n → ℂ) (he : star e ⬝ᵥ e = 1) (w : Fin m → Fin n → ℂ)
    (hw : ∀ b, star e ⬝ᵥ w b = 0) (a : ℂ) (c : Fin m → ℂ) (v : Fin (m + 1) → Fin n → ℂ)
    (h0 : v 0 = a • e) (hs : ∀ b, v b.succ = w b + c b • e) :
    (Matrix.of fun i j => star (v i) ⬝ᵥ v j).det =
      (Complex.normSq a : ℂ) * (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by sorry
