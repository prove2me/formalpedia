-- Prove2me | Theorems.Thm_GroundTheory_Global_SUnit_finrank_eq
-- name    : GroundTheory.Global.SUnit.finrank_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:26.780262+00:00
-- url     : https://prove2.me/theorems/7fec3ddb-854b-451c-80b4-8c4f6d62c595
-- title:
--   SUnit: finrank eq
-- statement:
--   The SUnit construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L161-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L161-L165

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
import Definitions.Def_GroundTheory_GlobalFields_SUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.SUnit
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite S]

theorem GroundTheory.Global.SUnit.finrank_eq : finrank ℤ (Additive (S.unit K)) = Units.rank K + Nat.card S := by sorry
