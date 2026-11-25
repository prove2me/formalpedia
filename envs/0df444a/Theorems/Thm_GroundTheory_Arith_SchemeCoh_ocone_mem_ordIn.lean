-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_mem_ordIn
-- name    : GroundTheory.Arith.SchemeCoh.ocone_mem_ordIn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:19.908043+00:00
-- url     : https://prove2.me/theorems/222b4432-9d24-48b3-b5a2-7fb3b0bb96e4
-- title:
--   Scheme Coh: ocone mem ord In
-- statement:
--   The Scheme Coh construction uses the ocone mem ord In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L266-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L266-L279

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
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
open CategoryTheory
universe w
variable {ι : Type w}
variable [LinearOrder ι]

theorem GroundTheory.Arith.SchemeCoh.ocone_mem_ordIn {n m : ℕ} (i : Fin (m + 1) → ι) {c : Chain ι n}
    (hc : c ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i))) :
    ocone (minIdx i) c ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i)) := by sorry
