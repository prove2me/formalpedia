-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_of_strictMono
-- name    : GroundTheory.Arith.SchemeCoh.minIdx_of_strictMono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:28:01.636453+00:00
-- url     : https://prove2.me/theorems/2a9275ed-90da-46d4-8b34-4bfd4ad9146f
-- title:
--   Scheme Coh: min Idx of strict Mono
-- statement:
--   The Scheme Coh construction uses the min Idx of strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L254-L256

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

theorem GroundTheory.Arith.SchemeCoh.minIdx_of_strictMono {n : ℕ} {i : Fin (n + 1) → ι} (hi : StrictMono i) : minIdx i = i 0 := by sorry
