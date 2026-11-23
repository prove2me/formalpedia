-- Prove2me | Theorems.Thm_GlobalTheory_HeckeOne_isContAtOne_of_isHeckeL
-- name    : GlobalTheory.HeckeOne.isContAtOne_of_isHeckeL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:06.768749+00:00
-- url     : https://prove2.me/theorems/cd25f073-8295-48f1-800c-fde31c04419b
-- title:
--   Hecke One: is Cont At One of is Hecke L
-- statement:
--   The Hecke One construction uses the is Cont At One of is Hecke L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HeckeLEntireAndNonzeroAtOne.lean#L130-L131

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

theorem GlobalTheory.HeckeOne.isContAtOne_of_isHeckeL {χ : HChar K} {Λ : ℂ → ℂ} (h : IsHeckeL χ Λ) : IsContAtOne χ Λ := by sorry
