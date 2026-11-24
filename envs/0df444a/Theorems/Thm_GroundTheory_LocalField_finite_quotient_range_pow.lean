-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finite_quotient_range_pow
-- name    : GroundTheory.LocalField.finite_quotient_range_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:00.586261+00:00
-- url     : https://prove2.me/theorems/69ea1d19-987c-481e-bdf2-5284409f8ab0
-- title:
--   Local Field: finite quotient range pow
-- statement:
--   The Local Field construction uses the finite quotient range pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L195-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L195-L235

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.finite_quotient_range_pow {m : ℕ} (hm : (m : K) ≠ 0) :
    Finite (Kˣ ⧸ (powMonoidHom m : Kˣ →* Kˣ).range) := by sorry
