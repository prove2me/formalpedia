-- Prove2me | Theorems.Thm_GlobalTheory_HCXi_gram_mul_flag
-- name    : GlobalTheory.HCXi.gram_mul_flag
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:49:55.413389+00:00
-- url     : https://prove2.me/theorems/c9597e5f-0754-442a-8a02-f22e5e71a1ee
-- title:
--   HCXi: gram mul flag
-- statement:
--   The HCXi construction uses the gram mul flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HalfVolumeEquivariant.lean#L25-L35

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

theorem GlobalTheory.HCXi.gram_mul_flag (k r : ℕ) (hk : 1 ≤ k) (g p : Mat k r) (hp : p ∈ Pset k r)
    (a : Fin (r + 1)) : gram k r (g * p) a = gram k r g a * gram k r p a := by sorry
