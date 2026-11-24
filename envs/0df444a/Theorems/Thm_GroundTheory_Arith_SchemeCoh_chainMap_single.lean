-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_chainMap_single
-- name    : GroundTheory.Arith.SchemeCoh.chainMap_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:29.375046+00:00
-- url     : https://prove2.me/theorems/1b0a7d13-8016-4cd9-b3f9-488bd20430c2
-- title:
--   Scheme Coh: chain Map single
-- statement:
--   The Scheme Coh construction uses the chain Map single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L18-L20

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

theorem GroundTheory.Arith.SchemeCoh.chainMap_single {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (i : Fin (n + 1) → ι) (z : ℤ) :
    chainMap θ (Finsupp.single i z) = Finsupp.single (i ∘ θ) z := by sorry
