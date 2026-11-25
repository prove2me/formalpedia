-- Prove2me | Theorems.Thm_GroundTheory_Global_SUnit_dvd_natCard_torsion
-- name    : GroundTheory.Global.SUnit.dvd_natCard_torsion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:39:34.870592+00:00
-- url     : https://prove2.me/theorems/f71e8d9d-dc33-4b29-a57d-486af9bb01a3
-- title:
--   SUnit: dvd nat Card torsion
-- statement:
--   The SUnit construction uses the dvd nat Card torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L92-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L92-L110

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
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
open NumberField IsDedekindDomain Module
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
open GroundTheory.Global.SUnit

theorem GroundTheory.Global.SUnit.dvd_natCard_torsion (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n] :
    n ∣ Nat.card (CommGroup.torsion (S.unit K)) := by sorry
