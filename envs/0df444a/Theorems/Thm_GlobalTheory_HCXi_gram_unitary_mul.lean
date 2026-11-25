-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_gram_unitary_mul
-- name    : GlobalTheory.HCXi.gram_unitary_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:02.075878+00:00
-- url     : https://prove2.me/theorems/ce407609-41c3-5bb4-a494-b5e965a7999f
-- title:
--   HCXi: gram unitary mul
-- statement:
--   The HCXi construction uses the gram unitary mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L17-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FrameIsotropicOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GramMinorDetTriangularMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HalfVolumeEquivariant
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
open GlobalTheory GlobalTheory.HCXi

theorem GlobalTheory.HCXi.gram_unitary_mul (k r : ℕ) (κ g : Mat k r) (hκ : κᴴ * κ = 1) (a : Fin (r + 1)) :
    gram k r (κ * g) a = gram k r g a := by sorry
