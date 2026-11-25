-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_kaehlerCoeff_smul
-- name    : GroundTheory.Arith.SchemeCoh.kaehlerCoeff_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:51.323122+00:00
-- url     : https://prove2.me/theorems/8053463a-84ae-4a36-ba56-9bd253aaf966
-- title:
--   Scheme Coh: kaehler Coeff smul
-- statement:
--   The Scheme Coh construction uses the kaehler Coeff smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L177-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/KaehlerPlace.lean#L177-L179

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

theorem GroundTheory.Arith.SchemeCoh.kaehlerCoeff_smul {t : K} (ht : D k K t ≠ 0) (f : K) (ω : Ω[K⁄k]) :
    kaehlerCoeff t (f • ω) = f * kaehlerCoeff t ω := by sorry
