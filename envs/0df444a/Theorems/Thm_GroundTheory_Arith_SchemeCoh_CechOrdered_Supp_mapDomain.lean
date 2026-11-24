-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_Supp_mapDomain
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.mapDomain
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:55.823331+00:00
-- url     : https://prove2.me/theorems/c90e6d22-e1e9-4307-b514-139a9aef1c1a
-- title:
--   Supp: map Domain
-- statement:
--   The Supp construction uses the map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L146-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L146-L155

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

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.Supp.mapDomain {r : ℕ} {R : (Fin (r + 1) → ι) → Prop}
    (f : (Fin (q + 1) → ι) → (Fin (r + 1) → ι)) {z : Chain ι q} (hz : Supp Q z)
    (h : ∀ t, Q t → R (f t)) : Supp R (Finsupp.mapDomain f z) := by sorry
