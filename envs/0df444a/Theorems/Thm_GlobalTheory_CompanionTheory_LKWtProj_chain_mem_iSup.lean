-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_chain_mem_iSup
-- name    : GlobalTheory.CompanionTheory.LKWtProj.chain_mem_iSup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:18.758222+00:00
-- url     : https://prove2.me/theorems/a575f2e7-8245-405e-951d-7463fca01dfc
-- title:
--   LKWt Proj: chain mem i Sup
-- statement:
--   The LKWt Proj construction uses the chain mem i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L64-L83

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

theorem GlobalTheory.CompanionTheory.LKWtProj.chain_mem_iSup {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (h : ∀ v : V, v ∈ ⨆ μ : ℂ, (E c c).eigenspace μ)
    (t : Cn n V) : t ∈ ⨆ μ : ℂ, (Ft ε E c).eigenspace μ := by sorry
