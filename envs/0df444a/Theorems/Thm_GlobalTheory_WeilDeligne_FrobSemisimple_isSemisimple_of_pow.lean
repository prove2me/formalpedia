-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_FrobSemisimple_isSemisimple_of_pow
-- name    : GlobalTheory.WeilDeligne.FrobSemisimple.isSemisimple_of_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:53.821607+00:00
-- url     : https://prove2.me/theorems/59a2dabb-f028-42d7-a4f4-97976b049545
-- title:
--   Frob Semisimple: is Semisimple of pow
-- statement:
--   The Frob Semisimple construction uses the is Semisimple of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrob.lean#L16-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/WeilGroupIsSemisimpleOfSemisimpleFrob.lean#L16-L35

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

theorem GlobalTheory.WeilDeligne.FrobSemisimple.isSemisimple_of_pow {g : End ℂ V} (hg : IsUnit g) {m : ℕ} (hm : 0 < m)
    (hs : (g ^ m).IsSemisimple) : g.IsSemisimple := by sorry
