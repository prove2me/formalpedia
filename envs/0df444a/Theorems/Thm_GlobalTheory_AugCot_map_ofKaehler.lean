-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_map_ofKaehler
-- name    : GlobalTheory.AugCot.map_ofKaehler
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:00.833748+00:00
-- url     : https://prove2.me/theorems/11f48667-3a2e-494b-9eb9-29194f8ca8e0
-- title:
--   Aug Cot: map of Kaehler
-- statement:
--   The Aug Cot construction uses the map of Kaehler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L318-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L318-L329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}

theorem GlobalTheory.AugCot.map_ofKaehler [Algebra A B] [IsScalarTower R A B]
    (h : εB.comp (IsScalarTower.toAlgHom R A B) = εA) (m : Ω[A⁄R]) :
    map _ h (ofKaehler εA m) = ofKaehler εB (KaehlerDifferential.map R R A B m) := by sorry
