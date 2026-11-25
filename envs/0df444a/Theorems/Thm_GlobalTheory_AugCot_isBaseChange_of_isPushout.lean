-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_isBaseChange_of_isPushout
-- name    : GlobalTheory.AugCot.isBaseChange_of_isPushout
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:51.827398+00:00
-- url     : https://prove2.me/theorems/89ac3caf-5bec-5706-8d68-13a428a5156a
-- title:
--   Aug Cot: is Base Change of is Pushout
-- statement:
--   The Aug Cot construction uses the is Base Change of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L616-L620
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L616-L620

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

theorem GlobalTheory.AugCot.isBaseChange_of_isPushout [Algebra A A'] [IsScalarTower R A A']
    [hP : Algebra.IsPushout R R' A A']
    (h : ∀ a, ε' (IsScalarTower.toAlgHom R A A' a) = algebraMap R R' (ε a)) :
    IsBaseChange R' (mapBase (IsScalarTower.toAlgHom R A A') h) := by sorry
