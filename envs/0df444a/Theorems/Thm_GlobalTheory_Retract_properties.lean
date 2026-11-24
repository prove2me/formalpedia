-- Prove2me | Theorems.Thm_GlobalTheory_Retract_properties
-- name    : GlobalTheory.Retract.properties
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:48.367683+00:00
-- url     : https://prove2.me/theorems/7c2265e6-0f40-4757-8d13-e2afa5fd4218
-- title:
--   Retract: properties
-- statement:
--   The Retract construction uses the properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L342-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L342-L354

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
  (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
include hir hr

theorem GlobalTheory.Retract.properties :
    (LocallyOfFiniteType g → LocallyOfFiniteType f) ∧
    (LocallyOfFinitePresentation g → LocallyOfFinitePresentation f) ∧
    (Flat g → Flat f) ∧ (Smooth g → Smooth f) ∧ (Etale g → Etale f) ∧
    (QuasiCompact g → QuasiCompact f) ∧ (IsSeparated g → IsSeparated f) ∧
    (UniversallyClosed g → UniversallyClosed f) ∧ (IsProper g → IsProper f) ∧
    (IsFinite g → IsFinite f) ∧ (GeometricallyConnected g → GeometricallyConnected f) ∧
    Surjective r ∧ (IsSeparated g → IsClosedImmersion i) := by sorry
