-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_convergesAt_zcoeff_incl
-- name    : GroundTheory.PAdicHodge.WittTilt.convergesAt_zcoeff_incl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:55.099031+00:00
-- url     : https://prove2.me/theorems/84ff9847-a5e2-445f-85c8-32ccaad336e8
-- title:
--   Witt Tilt: converges At zcoeff incl
-- statement:
--   The Witt Tilt construction uses the converges At zcoeff incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonNorm.lean#L31-L39

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector Laurent
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p

theorem GroundTheory.PAdicHodge.WittTilt.convergesAt_zcoeff_incl (x : AInf K p) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt ((teichLift K p).zcoeff (incl K p x)) ρ := by sorry
