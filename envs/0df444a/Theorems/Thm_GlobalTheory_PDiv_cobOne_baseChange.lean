-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cobOne_baseChange
-- name    : GlobalTheory.PDiv.cobOne_baseChange
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:47:23.839403+00:00
-- url     : https://prove2.me/theorems/e3282fe9-e836-5642-947c-31c1f08628c5
-- title:
--   PDiv: cob One base Change
-- statement:
--   The PDiv construction uses the cob One base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionsFlatBaseChangeBijective.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionsFlatBaseChangeBijective.lean#L9-L24

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionsFlatBaseChangeBijective
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory GlobalTheory.PDiv
variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [CommRing R']
  [Algebra R R']

theorem GlobalTheory.PDiv.cobOne_baseChange :
    cobOne R' (R' ⊗[R] A) = (AlgebraTensorModule.distribBaseChange R R' A A).toLinearMap ∘ₗ
      (cobOne R A).baseChange R' := by sorry
