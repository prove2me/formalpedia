-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_image_norm_tilt
-- name    : GroundTheory.PAdicHodge.image_norm_tilt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:32.851363+00:00
-- url     : https://prove2.me/theorems/d33455b1-a40e-47cc-ab69-9bfe56cc8cbe
-- title:
--   PAdic Hodge: image norm tilt
-- statement:
--   The PAdic Hodge construction uses the image norm tilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L268-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L268-L280

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_TiltCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
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
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "♮" x:max => ((PreTilt.untilt x : normInteger K) : K)

theorem GroundTheory.PAdicHodge.image_norm_tilt :
    (fun x : K♭ => ‖x‖) '' {0}ᶜ = (fun y : K => ‖y‖) '' {0}ᶜ := by sorry
