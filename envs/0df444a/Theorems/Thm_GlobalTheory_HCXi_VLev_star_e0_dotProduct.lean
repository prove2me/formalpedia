-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_VLev_star_e0_dotProduct
-- name    : GlobalTheory.HCXi.VLev.star_e0_dotProduct
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:25:45.453736+00:00
-- url     : https://prove2.me/theorems/087e3071-b427-51ff-991b-3c54c38ef0c3
-- title:
--   VLev: star e0 dot Product
-- statement:
--   The VLev construction uses the star e0 dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeLeviRecursion.lean#L95-L97

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

theorem GlobalTheory.HCXi.VLev.star_e0_dotProduct (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ v = v (eI k (1 + r') (a0 r')) := by sorry
