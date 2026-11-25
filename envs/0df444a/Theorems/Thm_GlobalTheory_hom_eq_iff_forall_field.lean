-- Prove2me | Theorems.Thm_GlobalTheory_hom_eq_iff_forall_field
-- name    : GlobalTheory.hom_eq_iff_forall_field
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:42.039603+00:00
-- url     : https://prove2.me/theorems/168cfe8f-ade3-5611-9f5d-6eb6db239ca5
-- title:
--   Global Theory: hom eq iff forall field
-- statement:
--   The Global Theory construction uses the hom eq iff forall field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L17-L21

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

theorem GlobalTheory.hom_eq_iff_forall_field [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g := by sorry
