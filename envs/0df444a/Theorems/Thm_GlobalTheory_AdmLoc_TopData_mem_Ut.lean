-- Prove2me | Theorems.Thm_GlobalTheory_AdmLoc_TopData_mem_Ut
-- name    : GlobalTheory.AdmLoc.TopData.mem_Ut
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:24.192005+00:00
-- url     : https://prove2.me/theorems/32e500bf-f971-580d-ab16-412961c050be
-- title:
--   Top Data: mem Ut
-- statement:
--   The Top Data construction uses the mem Ut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L85-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MkMemAdmissibleAtIffCocycle.lean#L85-L85

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
open GlobalTheory.AdmLoc.TopData
variable {n r : ℕ} (D : TopData n r)

theorem GlobalTheory.AdmLoc.TopData.mem_Ut (i : ZMod n) {u : ℤ} (hu : u ∈ D.Ut i) : 1 ≤ u ∧ u ≤ (D.h i : ℤ) - 1 := by sorry
