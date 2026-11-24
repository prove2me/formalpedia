-- Prove2me | Theorems.Thm_GroundTheory_Arith_Etale_exists_modules_linearEquiv
-- name    : GroundTheory.Arith.Etale.exists_modules_linearEquiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:45.08856+00:00
-- url     : https://prove2.me/theorems/c718da10-b5de-4835-be94-41aaf3d6e038
-- title:
--   Etale: exists modules linear Equiv
-- statement:
--   The Etale construction uses the exists modules linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/EtaleCompletion/PullbackAffine.lean#L95-L109

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_ModulesPullback
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u

theorem GroundTheory.Arith.Etale.exists_modules_linearEquiv (R : CommRingCat.{u}) (Q : Type u) [AddCommGroup Q]
    [Module Γ(Spec R, ⊤) Q] :
    ∃ P : (Spec R).Modules, Nonempty (Γ(P, ⊤) ≃ₗ[Γ(Spec R, ⊤)] Q) := by sorry
