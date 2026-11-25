-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_omegaLevel_one_bijective
-- name    : GlobalTheory.PDivGroup.omegaLevel_one_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:39:01.439448+00:00
-- url     : https://prove2.me/theorems/ed140206-c8ec-4b25-bf01-9905979d4ad4
-- title:
--   PDiv Group: omega Level one bijective
-- statement:
--   The PDiv Group construction uses the omega Level one bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L184-L187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem GlobalTheory.PDivGroup.omegaLevel_one_bijective (hp : (p : R) = 0) : Function.Bijective (G.omegaLevel 1) := by sorry
