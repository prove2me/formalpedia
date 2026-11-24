-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
-- name    : GroundTheory.Arith.SchemeCoh.lin_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:12.655483+00:00
-- url     : https://prove2.me/theorems/30353658-b927-4e8d-932a-79e52a7acc93
-- title:
--   Scheme Coh: lin single
-- statement:
--   The Scheme Coh construction uses the lin single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L67-L69

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

theorem GroundTheory.Arith.SchemeCoh.lin_single {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) (j : Fin (m + 1) → ι) (z : ℤ) :
    lin f (Finsupp.single j z) = z • f j := by sorry
