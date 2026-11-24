-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_le
-- name    : GroundTheory.Arith.SchemeCoh.minIdx_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:38.867793+00:00
-- url     : https://prove2.me/theorems/0626ffcd-2a4f-4661-aca0-16372161c3fd
-- title:
--   Scheme Coh: min Idx le
-- statement:
--   The Scheme Coh construction uses the min Idx le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L247-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L247-L248

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

theorem GroundTheory.Arith.SchemeCoh.minIdx_le {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)) : minIdx i ≤ i a := by sorry
