-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_single_mem_rangeIn
-- name    : GroundTheory.Arith.SchemeCoh.single_mem_rangeIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:52.05398+00:00
-- url     : https://prove2.me/theorems/b5666be9-21e4-4808-88dd-df98c4da1944
-- title:
--   Scheme Coh: single mem range In
-- statement:
--   The Scheme Coh construction uses the single mem range In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L89-L91

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

theorem GroundTheory.Arith.SchemeCoh.single_mem_rangeIn {n : ℕ} (i : Fin (n + 1) → ι) (z : ℤ) :
    Finsupp.single i z ∈ Finsupp.supported ℤ ℤ (rangeIn (Set.range i)) := by sorry
