-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_proj_eq_zero_of_not_injective
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.proj_eq_zero_of_not_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:30.407582+00:00
-- url     : https://prove2.me/theorems/e4e0a860-a544-488b-a6fa-22b5b0c62bc2
-- title:
--   Cech Ordered: proj eq zero of not injective
-- statement:
--   The Cech Ordered construction uses the proj eq zero of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L387-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L387-L401

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
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
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable [LinearOrder ι]

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.proj_eq_zero_of_not_injective (q : ℕ) (i : Fin (q + 1) → ι)
    (hi : ¬ Function.Injective i) : proj q i = 0 := by sorry
