-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cotBaseChange_d
-- name    : GlobalTheory.PDiv.cotBaseChange_d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:49:59.234946+00:00
-- url     : https://prove2.me/theorems/9cb2f797-e4c5-5014-9273-a8603892c96b
-- title:
--   PDiv: cot Base Change d
-- statement:
--   The PDiv construction uses the cot Base Change d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean#L37-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
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
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv
variable {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A]
  [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R']

theorem GlobalTheory.PDiv.cotBaseChange_d (φ : CartierDual R A) :
    cotBaseChange R' (dUnit R' (CartierDual.baseChange R R' A ((1 : R') ⊗ₜ φ))) =
      (1 : R') ⊗ₜ dUnit R φ := by sorry
