-- Prove2me | Theorems.Thm_GlobalTheory_T_primitive_semilinearLift_baseChange_bijective
-- name    : GlobalTheory.T.primitive_semilinearLift_baseChange_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:01:25.050773+00:00
-- url     : https://prove2.me/theorems/bcf50f55-8553-40ab-bee4-73ba0936d635
-- title:
--   T: primitive semilinear Lift base Change bijective
-- statement:
--   The T construction uses the primitive semilinear Lift base Change bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijectiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijectiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.primitive_semilinearLift_baseChange_bijective : ∀ {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R'] [Algebra R R'], Module.Projective R (Cot R (CartierDual R A)) → Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by sorry
