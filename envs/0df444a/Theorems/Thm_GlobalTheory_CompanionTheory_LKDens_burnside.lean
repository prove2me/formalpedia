-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKDens_burnside
-- name    : GlobalTheory.CompanionTheory.LKDens.burnside
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:26.547653+00:00
-- url     : https://prove2.me/theorems/67673283-26a2-4422-ac5e-a959beb5087d
-- title:
--   LKDens: burnside
-- statement:
--   The LKDens construction uses the burnside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/RhoSurj.lean#L14-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/RhoSurj.lean#L14-L41

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_RhoSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKDens
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KStab)
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.LKDens.burnside {A : Type} [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V)
    (hnt : Nontrivial V) (hirr : ∀ W : Submodule ℂ V, (∀ a : A, ∀ w ∈ W, ρ a w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by sorry
