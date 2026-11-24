-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
-- name    : GlobalTheory.AugCot.baseChangeEquiv_tmul_d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:45:35.914857+00:00
-- url     : https://prove2.me/theorems/c322d323-38e2-4e9e-8d0d-6f3e19c5761b
-- title:
--   Aug Cot: base Change Equiv tmul d
-- statement:
--   The Aug Cot construction uses the base Change Equiv tmul d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L643-L645
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L643-L645

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

theorem GlobalTheory.AugCot.baseChangeEquiv_tmul_d (r : R') (a : A) :
    baseChangeEquiv R' ε (r ⊗ₜ d ε a) = r • d _ (1 ⊗ₜ a) := by sorry
