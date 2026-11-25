-- Prove2me | Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_field_algebra
-- name    : GlobalTheory.over_hom_eq_iff_forall_field_algebra
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:44.585461+00:00
-- url     : https://prove2.me/theorems/c39eee94-fb9a-4dd6-89d2-d444a2e5f5a0
-- title:
--   Global Theory: over hom eq iff forall field algebra
-- statement:
--   The Global Theory construction uses the over hom eq iff forall field algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L54-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
variable {T Y S : Scheme.{u}}
variable {R : Type u} [CommRing R]

theorem GlobalTheory.over_hom_eq_iff_forall_field_algebra {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom] {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] [Algebra R k]
      (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ T), x ≫ f = x ≫ g := by sorry
