-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_support_finite
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.support_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:51.799802+00:00
-- url     : https://prove2.me/theorems/1c519816-2695-4a39-bd97-387b4e5da10b
-- title:
--   Hecke Coinv: support finite
-- statement:
--   The Hecke Coinv construction uses the support finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L43-L51

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}

theorem GlobalTheory.CompanionTheory.HeckeCoinv.support_finite [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    (Function.support fun γ : Γ => f (γ • x)).Finite := by sorry
