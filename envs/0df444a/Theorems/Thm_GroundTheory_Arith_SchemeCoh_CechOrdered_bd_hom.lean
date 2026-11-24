-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_bd_hom
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.bd_hom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:57.175033+00:00
-- url     : https://prove2.me/theorems/cd65b65d-793a-4bd9-bab5-d4b70cd034b1
-- title:
--   Cech Ordered: bd hom
-- statement:
--   The Cech Ordered construction uses the bd hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L423-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L423-L444

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

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.bd_hom : ∀ (q : ℕ) (i : Fin (q + 2) → ι),
    bd (q + 1) (hom (q + 1) i) =
      Finsupp.single i 1 - proj (q + 1) i - lin (hom q) (bd q (Finsupp.single i 1))
  := by sorry
