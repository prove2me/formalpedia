-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslSpan_span_eq_top
-- name    : GlobalTheory.ThetaTranslSpan.span_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:03.226392+00:00
-- url     : https://prove2.me/theorems/e7b27dc3-e10b-4bb1-82e6-0391d54e082a
-- title:
--   Theta Transl Span: span eq top
-- statement:
--   The Theta Transl Span construction uses the span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsImEqLattice.lean#L106-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsImEqLattice.lean#L106-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem GlobalTheory.ThetaTranslSpan.span_eq_top (hH : Hm.PosDef) (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : ∀ v, (∀ a ∈ Λ, ∃ k : ℤ, (star v ⬝ᵥ Hm.mulVec a).im = k) → v ∈ Λ) :
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := by sorry
