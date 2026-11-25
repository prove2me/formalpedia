-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_FrobSemisimple_minpoly_eval_zero_ne_zero
-- name    : GlobalTheory.WeilDeligne.FrobSemisimple.minpoly_eval_zero_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:04:27.323537+00:00
-- url     : https://prove2.me/theorems/44fe55e1-8ced-59f3-8541-c5b775190c29
-- title:
--   Frob Semisimple: minpoly eval zero ne zero
-- statement:
--   The Frob Semisimple construction uses the minpoly eval zero ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrob.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrob.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.FrobSemisimple
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem GlobalTheory.WeilDeligne.FrobSemisimple.minpoly_eval_zero_ne_zero {f : End ℂ V} (hf : IsUnit f) : (minpoly ℂ f).eval 0 ≠ 0 := by sorry
