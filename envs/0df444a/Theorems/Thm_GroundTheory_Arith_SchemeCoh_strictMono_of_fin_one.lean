-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_strictMono_of_fin_one
-- name    : GroundTheory.Arith.SchemeCoh.strictMono_of_fin_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:43.015513+00:00
-- url     : https://prove2.me/theorems/1d451833-c98a-4ee7-983f-a1d81586d2e7
-- title:
--   Scheme Coh: strict Mono of fin one
-- statement:
--   The Scheme Coh construction uses the strict Mono of fin one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L169-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean#L169-L171

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

theorem GroundTheory.Arith.SchemeCoh.strictMono_of_fin_one (j : Fin 1 → ι) : StrictMono j := by sorry
