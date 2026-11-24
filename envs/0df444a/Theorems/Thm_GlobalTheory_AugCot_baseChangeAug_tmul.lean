-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
-- name    : GlobalTheory.AugCot.baseChangeAug_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:01.803605+00:00
-- url     : https://prove2.me/theorems/2d14f726-0b48-429c-973c-0b33781f770a
-- title:
--   Aug Cot: base Change Aug tmul
-- statement:
--   The Aug Cot construction uses the base Change Aug tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L628-L630
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L628-L630

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
variable {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra R A'] [IsScalarTower R R' A']
  {ε : A →ₐ[R] R} {ε' : A' →ₐ[R'] R'}

theorem GlobalTheory.AugCot.baseChangeAug_tmul (r : R') (a : A) :
    baseChangeAug R' ε (r ⊗ₜ a) = r * algebraMap R R' (ε a) := by sorry
