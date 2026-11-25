-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_SemiBialgHom_levelRig_mk
-- name    : GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:38:40.290301+00:00
-- url     : https://prove2.me/theorems/bfa96bfe-20e1-46a8-bc87-9cb728de76ea
-- title:
--   Semi Bialg Hom: level Rig mk
-- statement:
--   The Semi Bialg Hom construction uses the level Rig mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L94-L96

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
open GlobalTheory.PDiv
variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {A A' : Type} [CommRing A]
  [Bialgebra R A] [CommRing A'] [Bialgebra R' A']
variable [IsCocomm R A] [IsCocomm R' A']

theorem GlobalTheory.PDiv.SemiBialgHom.levelRig_mk (f : SemiBialgHom σ A A')
    (x : symCocycles R A × Cot R A) :
    f.levelRig (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f.levelPair x) := by sorry

attribute [defeq] GlobalTheory.PDiv.SemiBialgHom.levelRig_mk
