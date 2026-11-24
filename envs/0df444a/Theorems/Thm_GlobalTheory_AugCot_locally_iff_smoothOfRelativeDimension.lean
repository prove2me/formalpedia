-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_locally_iff_smoothOfRelativeDimension
-- name    : GlobalTheory.AugCot.locally_iff_smoothOfRelativeDimension
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:45:04.056931+00:00
-- url     : https://prove2.me/theorems/6b633fc4-a344-488f-bfa8-73f02b61c2b2
-- title:
--   Aug Cot: locally iff smooth Of Relative Dimension
-- statement:
--   The Aug Cot construction uses the locally iff smooth Of Relative Dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L770-L774
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L770-L774

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
open AlgebraicGeometry

theorem GlobalTheory.AugCot.locally_iff_smoothOfRelativeDimension :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A) ↔
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by sorry
