-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_primTangent_bijective
-- name    : GlobalTheory.PDiv.primTangent_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:44.793413+00:00
-- url     : https://prove2.me/theorems/d97b6bf0-92c1-4eba-8e63-48216d623046
-- title:
--   PDiv: prim Tangent bijective
-- statement:
--   The PDiv construction uses the prim Tangent bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionCartierDualTangentBijective.lean#L22-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdditiveFunctionCartierDualTangentBijective.lean#L22-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdditiveFunctionCartierDualTangentBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.PDiv

theorem GlobalTheory.PDiv.primTangent_bijective {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] :
    Function.Bijective (primTangent R A) := by sorry
