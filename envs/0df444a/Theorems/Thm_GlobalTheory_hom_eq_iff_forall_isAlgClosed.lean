-- Prove2me | Theorems.Thm_GlobalTheory_hom_eq_iff_forall_isAlgClosed
-- name    : GlobalTheory.hom_eq_iff_forall_isAlgClosed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:48:07.336881+00:00
-- url     : https://prove2.me/theorems/af8f8453-6a57-41e6-9680-9d7bae7cf762
-- title:
--   Global Theory: hom eq iff forall is Alg Closed
-- statement:
--   The Global Theory construction uses the hom eq iff forall is Alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/OverHomEqIffForallIsAlgClosedAlgebra.lean#L23-L31

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

theorem GlobalTheory.hom_eq_iff_forall_isAlgClosed [IsReduced T] (s : Y ⟶ S) [IsSeparated s] {f g : T ⟶ Y}
    (h : f ≫ s = g ≫ s) :
    f = g ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ T), x ≫ f = x ≫ g := by sorry
