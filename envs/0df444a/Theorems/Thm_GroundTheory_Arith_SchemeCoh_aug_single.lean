-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_aug_single
-- name    : GroundTheory.Arith.SchemeCoh.aug_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:40.616476+00:00
-- url     : https://prove2.me/theorems/037fe47d-2960-4fc4-a67c-828644d05531
-- title:
--   Scheme Coh: aug single
-- statement:
--   The Scheme Coh construction uses the aug single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L53-L54

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

theorem GroundTheory.Arith.SchemeCoh.aug_single (j : Fin 1 → ι) (z : ℤ) : aug (Finsupp.single j z) = z := by sorry
