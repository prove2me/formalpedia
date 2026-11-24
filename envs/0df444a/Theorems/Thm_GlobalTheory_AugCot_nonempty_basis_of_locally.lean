-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_nonempty_basis_of_locally
-- name    : GlobalTheory.AugCot.nonempty_basis_of_locally
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:10.514899+00:00
-- url     : https://prove2.me/theorems/53519559-3017-4e96-b46f-cba636829d46
-- title:
--   Aug Cot: nonempty basis of locally
-- statement:
--   The Aug Cot construction uses the nonempty basis of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L762-L766
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L762-L766

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
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}

theorem GlobalTheory.AugCot.nonempty_basis_of_locally [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Nonempty (Module.Basis (Fin n) R (AugCot ε)) := by sorry
