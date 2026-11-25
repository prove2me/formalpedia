-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_preTiltMap
-- name    : GroundTheory.PAdicHodge.fontaineTheta_map_preTiltMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:59.449024+00:00
-- url     : https://prove2.me/theorems/c9a78cd0-1522-405f-b866-6519b004ec18
-- title:
--   PAdic Hodge: fontaine Theta map pre Tilt Map
-- statement:
--   The PAdic Hodge construction uses the fontaine Theta map pre Tilt Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltMap.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltMap.lean#L162-L170

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
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
variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪L♭" => PreTilt (normInteger L) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "L♭" => Tilt L NormedField.valuation (normInteger L) normInteger_integers p

theorem GroundTheory.PAdicHodge.fontaineTheta_map_preTiltMap (w : WittVector p 𝒪K♭) :
    WittVector.fontaineTheta (normInteger L) p (WittVector.map (preTiltMap p φ hφ) w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) := by sorry
