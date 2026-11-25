-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lift_algebraically_closed_point
-- name    : GlobalTheory.T.exists_lift_algebraically_closed_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:12.818369+00:00
-- url     : https://prove2.me/theorems/9011b79e-9fbb-411d-866b-41a14ab5e238
-- title:
--   T: exists lift algebraically closed point
-- statement:
--   The T construction uses the exists lift algebraically closed point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftAlgebraicallyClosedPointStatement.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftAlgebraicallyClosedPointStatement.lean#L6-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftAlgebraicallyClosedPoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftAlgebraicallyClosedPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_lift_algebraically_closed_point : ∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by sorry
