-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_ne_zero
-- name    : GroundTheory.Arith.SchemeCoh.kaehlerCoeff_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:48:40.092795+00:00
-- url     : https://prove2.me/theorems/aa88ac2b-0f93-4069-8eb3-5640ef679880
-- title:
--   Scheme Coh: kaehler Coeff ne zero
-- statement:
--   The Scheme Coh construction uses the kaehler Coeff ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L185-L190

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_KaehlerPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open GroundTheory.FunctionField KaehlerDifferential IntermediateField
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable [IsFunctionField k K]
variable [PerfectField k]

theorem GroundTheory.Arith.SchemeCoh.kaehlerCoeff_ne_zero {t : K} (ht : D k K t ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerCoeff t ω ≠ 0 := by sorry
