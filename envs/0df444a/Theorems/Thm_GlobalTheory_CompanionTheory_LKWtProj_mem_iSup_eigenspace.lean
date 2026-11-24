-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_mem_iSup_eigenspace
-- name    : GlobalTheory.CompanionTheory.LKWtProj.mem_iSup_eigenspace
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:17.861932+00:00
-- url     : https://prove2.me/theorems/956f172e-36a5-4092-a44b-7d8962d7e405
-- title:
--   LKWt Proj: mem i Sup eigenspace
-- statement:
--   The LKWt Proj construction uses the mem i Sup eigenspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L45-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L45-L58

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKWtProj
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem GlobalTheory.CompanionTheory.LKWtProj.mem_iSup_eigenspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : Module.End ℂ V)
    (hT : T.IsSymmetric) (S : Submodule ℂ V) [FiniteDimensional ℂ S] (hS : ∀ v ∈ S, T v ∈ S) (x : V) (hx : x ∈ S) :
    x ∈ ⨆ μ : ℂ, T.eigenspace μ := by sorry
