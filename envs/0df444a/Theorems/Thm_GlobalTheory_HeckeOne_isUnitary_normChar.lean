-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_isUnitary_normChar
-- name    : GlobalTheory.HeckeOne.isUnitary_normChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:25.309104+00:00
-- url     : https://prove2.me/theorems/0ee3c38a-248c-48b6-ac0a-edff038ba23e
-- title:
--   Hecke One: is Unitary norm Char
-- statement:
--   The Hecke One construction uses the is Unitary norm Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L78-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L78-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EntireEqOfHalfPlane
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HeckeLEntireAndNonzeroAtOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (Ideles eulerFactor IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleNorm)
open GlobalTheory GlobalTheory.HeckeOne
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.HeckeOne.isUnitary_normChar (t : ℝ) : (normChar K t).IsUnitary := by sorry
