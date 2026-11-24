-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_proj_of_strictMono
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.proj_of_strictMono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:16.375425+00:00
-- url     : https://prove2.me/theorems/cf5f1018-1751-4ebd-9f8b-8b73e956060c
-- title:
--   Cech Ordered: proj of strict Mono
-- statement:
--   The Cech Ordered construction uses the proj of strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L363-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L363-L385

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

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.proj_of_strictMono : ∀ (q : ℕ) (i : Fin (q + 1) → ι), StrictMono i →
    proj q i = Finsupp.single i 1
  := by sorry
