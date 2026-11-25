-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_VLev_gram_eq
-- name    : GlobalTheory.HCXi.VLev.gram_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:22:26.165086+00:00
-- url     : https://prove2.me/theorems/139db638-30e8-40c3-a7fc-10561db40a89
-- title:
--   VLev: gram eq
-- statement:
--   The VLev construction uses the gram eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L49-L54

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

theorem GlobalTheory.HCXi.VLev.gram_eq (k r : ℕ) (g : Mat k r) (j : Fin (r + 1)) :
    gram k r g j = (Matrix.of fun i i' : Fin (j.val + 1) =>
      star (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)) ⬝ᵥ
        (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i'))).det.re := by sorry
