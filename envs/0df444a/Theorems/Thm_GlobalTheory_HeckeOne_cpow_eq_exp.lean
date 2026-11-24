-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_cpow_eq_exp
-- name    : GlobalTheory.HeckeOne.cpow_eq_exp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:31.712884+00:00
-- url     : https://prove2.me/theorems/e3e33c27-c630-47b1-8d46-fd6f7b32281b
-- title:
--   Hecke One: cpow eq exp
-- statement:
--   The Hecke One construction uses the cpow eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L44-L51

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

theorem GlobalTheory.HeckeOne.cpow_eq_exp (x : Ideles K) (t : ℝ) :
    ((ideleNorm x : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((Circle.exp (t * Real.log (ideleNorm x)) : Circle) : ℂ) := by sorry
