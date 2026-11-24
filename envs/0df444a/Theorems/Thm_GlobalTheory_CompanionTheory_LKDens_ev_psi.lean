-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKDens_ev_psi
-- name    : GlobalTheory.CompanionTheory.LKDens.ev_psi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:52:07.015793+00:00
-- url     : https://prove2.me/theorems/899ca9eb-a563-472b-8883-6af9c805f5d5
-- title:
--   LKDens: ev psi
-- statement:
--   The LKDens construction uses the ev psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/RhoSurj.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/RhoSurj.lean#L50-L60

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

theorem GlobalTheory.CompanionTheory.LKDens.ev_psi (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (L : Submodule ℂ V) (hL : KStab ε E L)
    (r : FreeAlgebra ℂ (Fin n × Fin n)) : ∀ s : L, ev E (psi ε r) s = (rho ε E L hL r s : V) := by sorry
