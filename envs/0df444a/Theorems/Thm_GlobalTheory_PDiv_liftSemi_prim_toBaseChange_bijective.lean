-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_liftSemi_prim_toBaseChange_bijective
-- name    : GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:02:21.560372+00:00
-- url     : https://prove2.me/theorems/d165b739-f3cc-4758-9729-43fa2844fc2c
-- title:
--   PDiv: lift Semi prim to Base Change bijective
-- statement:
--   The PDiv construction uses the lift Semi prim to Base Change bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean#L60-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PrimitiveSemilinearLiftBaseChangeBijective.lean#L60-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PrimitiveSemilinearLiftBaseChangeBijective
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

theorem GlobalTheory.PDiv.liftSemi_prim_toBaseChange_bijective {R A : Type} (R' : Type) [CommRing R] [CommRing A]
    [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) := by sorry
