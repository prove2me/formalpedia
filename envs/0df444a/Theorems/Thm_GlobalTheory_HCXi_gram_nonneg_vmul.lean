-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_gram_nonneg_vmul
-- name    : GlobalTheory.HCXi.gram_nonneg_vmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:39.89685+00:00
-- url     : https://prove2.me/theorems/853baf8b-bffc-4472-a2ba-1be8d8703a79
-- title:
--   HCXi: gram nonneg vmul
-- statement:
--   The HCXi construction uses the gram nonneg vmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L11-L15

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

theorem GlobalTheory.HCXi.gram_nonneg_vmul (k r : ℕ) (g : Mat k r) (a : Fin (r + 1)) : 0 ≤ gram k r g a := by sorry
