-- Prove2me | Theorems.Thm_GlobalTheory_T_additiveFunctionCartierDualTangent_bijective
-- name    : GlobalTheory.T.additiveFunctionCartierDualTangent_bijective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:57:03.653305+00:00
-- url     : https://prove2.me/theorems/8873ed32-e761-4607-ab5e-e7e090bf4a43
-- title:
--   T: additive Function Cartier Dual Tangent bijective
-- statement:
--   The T construction uses the additive Function Cartier Dual Tangent bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionCartierDualTangentBijectiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionCartierDualTangentBijectiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijectiveStatement
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

theorem GlobalTheory.T.additiveFunctionCartierDualTangent_bijective : ∀ {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Projective R A] [IsCocomm R A], Function.Bijective (primTangent R A) := by sorry
