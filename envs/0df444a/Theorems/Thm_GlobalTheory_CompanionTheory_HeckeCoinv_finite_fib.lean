-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_finite_fib
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.finite_fib
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:41.168876+00:00
-- url     : https://prove2.me/theorems/bae382a7-4512-4ed6-a4a3-fb999d361f55
-- title:
--   Hecke Coinv: finite fib
-- statement:
--   The Hecke Coinv construction uses the finite fib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L26-L36

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

theorem GlobalTheory.CompanionTheory.HeckeCoinv.finite_fib [∀ x : X, Finite (MulAction.stabilizer Γ x)] (x y : X) :
    Finite {γ : Γ // γ • x = y} := by sorry
