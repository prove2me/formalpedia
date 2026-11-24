-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_Ft_commute
-- name    : GlobalTheory.CompanionTheory.LKWtProj.Ft_commute
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:18.034184+00:00
-- url     : https://prove2.me/theorems/3b09a429-ae8e-4cc2-9767-783eb12f8216
-- title:
--   LKWt Proj: Ft commute
-- statement:
--   The LKWt Proj construction uses the Ft commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L85-L97

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

theorem GlobalTheory.CompanionTheory.LKWtProj.Ft_commute {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε₀ ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) (c d : Fin n) : Commute (Ft ε₀ E c) (Ft ε₀ E d) := by sorry
