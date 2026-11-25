-- Prove2me | Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_field
-- name    : GlobalTheory.over_hom_eq_iff_forall_field
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:26.375783+00:00
-- url     : https://prove2.me/theorems/f92a4eb8-b063-44e2-8f50-62512876fd6a
-- title:
--   Global Theory: over hom eq iff forall field
-- statement:
--   The Global Theory construction uses the over hom eq iff forall field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L33-L39

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

theorem GlobalTheory.over_hom_eq_iff_forall_field {T Y : Over S} [IsReduced T.left] [IsSeparated Y.hom]
    {f g : T ⟶ Y} :
    f = g ↔ ∀ (k : Type u) [Field k] (t : Spec (.of k) ⟶ S) (x : Over.mk t ⟶ T),
      x ≫ f = x ≫ g := by sorry
