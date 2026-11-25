-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_preTiltMap
-- name    : GroundTheory.PAdicHodge.norm_preTiltMap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:33.414731+00:00
-- url     : https://prove2.me/theorems/31f9906a-62bb-5c98-9dd2-f9ff2c1a2e8b
-- title:
--   PAdic Hodge: norm pre Tilt Map
-- statement:
--   The PAdic Hodge construction uses the norm pre Tilt Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltMap.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltMap.lean#L94-L95

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

theorem GroundTheory.PAdicHodge.norm_preTiltMap (x : 𝒪K♭) : ‖preTiltMap p φ hφ x‖ = ‖x‖ := by sorry
