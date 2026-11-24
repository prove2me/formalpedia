-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_finsum_eq
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.finsum_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:14.474935+00:00
-- url     : https://prove2.me/theorems/f10f6eba-adeb-4128-82e8-8a2b503bf9b1
-- title:
--   Hecke Coinv: finsum eq
-- statement:
--   The Hecke Coinv construction uses the finsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L53-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L53-L77

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

theorem GlobalTheory.CompanionTheory.HeckeCoinv.finsum_eq [∀ x : X, Finite (MulAction.stabilizer Γ x)] (f : X →₀ ℂ) (x : X) :
    ∑ᶠ γ : Γ, f (γ • x) = f.sum fun z c => c * (cnt Γ x z : ℂ) := by sorry
