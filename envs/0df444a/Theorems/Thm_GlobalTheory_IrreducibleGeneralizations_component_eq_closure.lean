-- Prove2me | Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_component_eq_closure
-- name    : GlobalTheory.IrreducibleGeneralizations.component_eq_closure
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:21:36.34821+00:00
-- url     : https://prove2.me/theorems/4cfb4ff9-4156-49dd-8763-e1557d4c7093
-- title:
--   Irreducible Generalizations: component eq closure
-- statement:
--   The Irreducible Generalizations construction uses the component eq closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIrreducibleGeneralizations.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIrreducibleGeneralizations.lean#L17-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.IrreducibleGeneralizations
open AlgebraicGeometry Topology

theorem GlobalTheory.IrreducibleGeneralizations.component_eq_closure {X : Scheme.{u_1}} {x : X} [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure {y : X | y ⤳ x} := by sorry
