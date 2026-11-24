-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_VacLoc_GoodInh_exists_goodChar
-- name    : GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:10.996604+00:00
-- url     : https://prove2.me/theorems/e32ee38e-99dd-4499-a240-b7ef508f27d6
-- title:
--   Good Inh: exists good Char
-- statement:
--   The Good Inh construction uses the exists good Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DualNumberGraphFiltrationIsotropicOfSkew.lean#L95-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/DualNumberGraphFiltrationIsotropicOfSkew.lean#L95-L117

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.GoodInh
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CompanionTheory.VacLoc.GoodInh.exists_goodChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      (∃ ψ : AddChar k ℂ, GoodChar ψ 𝒪[k] 1) ∧
      ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ x, ‖ψ x‖ = 1) → ψ ≠ 1 → ∃ u : kˣ, GoodChar ψ 𝒪[k] u := by sorry
