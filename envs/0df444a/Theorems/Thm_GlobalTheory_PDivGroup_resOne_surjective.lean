-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_resOne_surjective
-- name    : GlobalTheory.PDivGroup.resOne_surjective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:36:57.925334+00:00
-- url     : https://prove2.me/theorems/c41a2228-9d5d-4dc2-b2ee-5eecfad08814
-- title:
--   PDiv Group: res One surjective
-- statement:
--   The PDiv Group construction uses the res One surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L117-L120

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

theorem GlobalTheory.PDivGroup.resOne_surjective (n : ℕ) : Function.Surjective (G.resOne n) := by sorry
