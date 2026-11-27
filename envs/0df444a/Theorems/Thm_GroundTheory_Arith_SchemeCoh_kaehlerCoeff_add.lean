-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_add
-- name    : GroundTheory.Arith.SchemeCoh.kaehlerCoeff_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:07.489664+00:00
-- url     : https://prove2.me/theorems/64a4bb7d-97fb-4031-8a6f-12b39fa83648
-- title:
--   Scheme Coh: kaehler Coeff add
-- statement:
--   The Scheme Coh construction uses the kaehler Coeff add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L181-L183

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

theorem GroundTheory.Arith.SchemeCoh.kaehlerCoeff_add {t : K} (ht : D k K t ≠ 0) (ω₁ ω₂ : Ω[K⁄k]) :
    kaehlerCoeff t (ω₁ + ω₂) = kaehlerCoeff t ω₁ + kaehlerCoeff t ω₂ := by sorry
