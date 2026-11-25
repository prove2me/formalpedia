-- Prove2me | Theorems.Thm_GlobalTheory_WeilDeligne_semisimplePart_mul_eq
-- name    : GlobalTheory.WeilDeligne.semisimplePart_mul_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T17:19:50.617865+00:00
-- url     : https://prove2.me/theorems/7df9ceeb-4ad2-5b22-9c16-176ae747580e
-- title:
--   Weil Deligne: semisimple Part mul eq
-- statement:
--   The Weil Deligne construction uses the semisimple Part mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFrobeniusSemisimplification.lean#L14-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsFrobeniusSemisimplification.lean#L14-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPowEqPowOfWeilDegreeEqSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_WeilGroupIsSemisimpleOfSemisimpleFrobStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsFrobeniusSemisimplification
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
variable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem GlobalTheory.WeilDeligne.semisimplePart_mul_eq {f s N : End ℂ V} {c : ℂ} (hc : Commute f s) (hs : s.IsSemisimple)
    (hn : IsNilpotent (f - s)) (h : f * N = c • (N * f)) : s * N = c • (N * s) := by sorry
