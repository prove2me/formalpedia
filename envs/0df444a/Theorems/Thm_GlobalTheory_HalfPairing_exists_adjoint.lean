-- Prove2me | Theorems.Thm_GlobalTheory_HalfPairing_exists_adjoint
-- name    : GlobalTheory.HalfPairing.exists_adjoint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:03:28.067702+00:00
-- url     : https://prove2.me/theorems/d7cfc7ad-de04-4fde-8413-9c20716f2641
-- title:
--   Half Pairing: exists adjoint
-- statement:
--   The Half Pairing construction uses the exists adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HalvesFreeAndAdjoint.lean#L95-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HalvesFreeAndAdjoint.lean#L95-L122

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HalfPairing

theorem GlobalTheory.HalfPairing.exists_adjoint {R P Q Z : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup Z] (s : R → R) (B : P → Q → Z) (hadd : ∀ u v w, B u (v + w) = B u v + B u w)
    (hbal : ∀ a u v, B u (a • v) = B (s a • u) v)
    (hnd : ∀ v w, (∀ u, B u v = B u w) → v = w)
    (hrep : ∀ (g : P →ₗ[R] P) (v : Q), ∃ w, ∀ u, B (g u) v = B u w) :
    ∃ adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q), (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : Q ≃ₗ[R] Q) (g : P ≃ₗ[R] P), (∀ u v, B (g u) v = B u (k v)) ↔ k = adj g := by sorry
