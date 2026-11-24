-- Prove2me | Theorems.Thm_GlobalTheory_Retract_over_properties
-- name    : GlobalTheory.Retract.over_properties
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:22:44.180801+00:00
-- url     : https://prove2.me/theorems/f086dd5b-47e6-48bf-a720-7e6617b976e4
-- title:
--   Retract: over properties
-- statement:
--   The Retract construction uses the over properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L365-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentation.lean#L365-L374

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
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.Retract.over_properties (h : CategoryTheory.Retract X Y) :
    (LocallyOfFiniteType Y.hom → LocallyOfFiniteType X.hom) ∧
    (LocallyOfFinitePresentation Y.hom → LocallyOfFinitePresentation X.hom) ∧
    (Flat Y.hom → Flat X.hom) ∧ (Smooth Y.hom → Smooth X.hom) ∧ (Etale Y.hom → Etale X.hom) ∧
    (QuasiCompact Y.hom → QuasiCompact X.hom) ∧ (IsSeparated Y.hom → IsSeparated X.hom) ∧
    (UniversallyClosed Y.hom → UniversallyClosed X.hom) ∧ (IsProper Y.hom → IsProper X.hom) ∧
    (IsFinite Y.hom → IsFinite X.hom) ∧
    (GeometricallyConnected Y.hom → GeometricallyConnected X.hom) ∧
    Surjective h.r.left ∧ (IsSeparated Y.hom → IsClosedImmersion h.i.left) := by sorry
