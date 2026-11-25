-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_smul_D
-- name    : GroundTheory.Arith.SchemeCoh.kaehlerCoeff_smul_D
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:56.752806+00:00
-- url     : https://prove2.me/theorems/3c2d5b94-1634-4c93-ba36-d566e5547c48
-- title:
--   Scheme Coh: kaehler Coeff smul D
-- statement:
--   The Scheme Coh construction uses the kaehler Coeff smul D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L165-L171

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

theorem GroundTheory.Arith.SchemeCoh.kaehlerCoeff_smul_D {t : K} (ht : D k K t ≠ 0) (ω : Ω[K⁄k]) :
    kaehlerCoeff t ω • D k K t = ω := by sorry
