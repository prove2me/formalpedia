-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_exists_proj
-- name    : GlobalTheory.CompanionTheory.LKWtProj.exists_proj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:42.692979+00:00
-- url     : https://prove2.me/theorems/c38047f6-8e71-4b32-875a-dd5ff75221f9
-- title:
--   LKWt Proj: exists proj
-- statement:
--   The LKWt Proj construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L15-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L15-L43

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

theorem GlobalTheory.CompanionTheory.LKWtProj.exists_proj {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (τ : ℂ) (t : M)
    (ht : t ∈ ⨆ μ : ℂ, F.eigenspace μ) :
    ∃ P : Module.End ℂ M, (∀ G, Commute F G → Commute P G) ∧
      (∀ W : Submodule ℂ M, (∀ x ∈ W, F x ∈ W) → ∀ x ∈ W, P x ∈ W) ∧
      (∀ y, F y = τ • y → P y = y) ∧ F (P t) = τ • P t := by sorry
