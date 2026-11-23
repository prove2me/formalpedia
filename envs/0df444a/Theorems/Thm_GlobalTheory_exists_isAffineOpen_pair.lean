-- Prove2me | Theorems.Thm_GlobalTheory_exists_isAffineOpen_pair
-- name    : GlobalTheory.exists_isAffineOpen_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:45.180066+00:00
-- url     : https://prove2.me/theorems/f86f0986-aa42-447f-bd86-458734c49e21
-- title:
--   Global Theory: exists is Affine Open pair
-- statement:
--   The Global Theory construction uses the exists is Affine Open pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsCompletionPointClosedPointMemOfSmooth.lean#L25-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem GlobalTheory.exists_isAffineOpen_pair (x : X) {O : X.Opens} (hx : x ∈ O) :
    ∃ (U : S.Opens) (V : X.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ V ≤ f ⁻¹ᵁ U ∧ V ≤ O ∧
      x ∈ V := by sorry
