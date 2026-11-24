-- Prove2me | Theorems.Thm_GlobalTheory_T_lattice_hom_submodule_fg_and_span_eq_top
-- name    : GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:51:24.230866+00:00
-- url     : https://prove2.me/theorems/66ecf9b8-55b0-4474-bf10-bf4a6813418e
-- title:
--   T: lattice hom submodule fg and span eq top
-- statement:
--   The T construction uses the lattice hom submodule fg and span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeHomSubmoduleFgAndSpanEqTopStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeHomSubmoduleFgAndSpanEqTopStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeHomSubmoduleFgAndSpanEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lattice_hom_submodule_fg_and_span_eq_top : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by sorry
