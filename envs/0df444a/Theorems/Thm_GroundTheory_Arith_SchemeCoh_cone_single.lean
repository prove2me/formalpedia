-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_cone_single
-- name    : GroundTheory.Arith.SchemeCoh.cone_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:19.134886+00:00
-- url     : https://prove2.me/theorems/cc09ab8b-1b7c-4f1a-8878-1b7e58e600c3
-- title:
--   Scheme Coh: cone single
-- statement:
--   The Scheme Coh construction uses the cone single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L115-L117

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

theorem GroundTheory.Arith.SchemeCoh.cone_single {n : ℕ} (s : ι) (i : Fin (n + 1) → ι) (z : ℤ) :
    cone s (Finsupp.single i z) = Finsupp.single (Fin.cons s i : Fin (n + 2) → ι) z := by sorry
