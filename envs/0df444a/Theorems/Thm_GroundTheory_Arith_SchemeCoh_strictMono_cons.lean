-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_strictMono_cons
-- name    : GroundTheory.Arith.SchemeCoh.strictMono_cons
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:17.681878+00:00
-- url     : https://prove2.me/theorems/7de4efca-0d38-43f2-a896-b03a71bf0172
-- title:
--   Scheme Coh: strict Mono cons
-- statement:
--   The Scheme Coh construction uses the strict Mono cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L149-L156

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

theorem GroundTheory.Arith.SchemeCoh.strictMono_cons {n : ℕ} {s : ι} {j : Fin (n + 1) → ι} (hj : StrictMono j) (hs : s < j 0) :
    StrictMono (Fin.cons s j : Fin (n + 2) → ι) := by sorry
