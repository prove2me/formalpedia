-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_preimage_of_isIso_morphismRestrict
-- name    : GroundTheory.Arith.SchemeCoh.exists_preimage_of_isIso_morphismRestrict
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:46.740213+00:00
-- url     : https://prove2.me/theorems/c4469b55-e359-45ac-8ee0-e8932a2093e4
-- title:
--   Scheme Coh: exists preimage of is Iso morphism Restrict
-- statement:
--   The Scheme Coh construction uses the exists preimage of is Iso morphism Restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/RestrictIso.lean#L53-L59

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
universe u
noncomputable section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem GroundTheory.Arith.SchemeCoh.exists_preimage_of_isIso_morphismRestrict {U : Y.Opens} [IsIso (f ∣_ U)] {y : Y}
    (hy : y ∈ U) : ∃ x : X, x ∈ f ⁻¹ᵁ U ∧ f.base x = y := by sorry
