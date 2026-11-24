-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
-- name    : GroundTheory.Arith.SchemeCoh.map_mem_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:01.194213+00:00
-- url     : https://prove2.me/theorems/e1d91662-d1d5-4379-bebd-4feb3f958f43
-- title:
--   Scheme Coh: map mem supported
-- statement:
--   The Scheme Coh construction uses the map mem supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L71-L76

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

theorem GroundTheory.Arith.SchemeCoh.map_mem_supported {m n : ℕ} (L : Chain ι m →+ Chain ι n) {S : Set (Fin (m + 1) → ι)}
    {T : Set (Fin (n + 1) → ι)}
    (h : ∀ j ∈ S, ∀ z : ℤ, L (Finsupp.single j z) ∈ Finsupp.supported ℤ ℤ T) {c : Chain ι m}
    (hc : c ∈ Finsupp.supported ℤ ℤ S) : L c ∈ Finsupp.supported ℤ ℤ T := by sorry
