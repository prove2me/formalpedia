-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_Supp_sub
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:42.73122+00:00
-- url     : https://prove2.me/theorems/e79df061-d9cb-475e-8d5e-e36c2f89b07b
-- title:
--   Supp: sub
-- statement:
--   The Supp construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L114-L116

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
variable {q : ℕ} {Q Q' : (Fin (q + 1) → ι) → Prop}

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.sub {z z' : Chain ι q} (hz : Supp Q z) (hz' : Supp Q z') : Supp Q (z - z') := by sorry
