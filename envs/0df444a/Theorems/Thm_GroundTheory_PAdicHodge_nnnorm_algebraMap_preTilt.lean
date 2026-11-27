-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_nnnorm_algebraMap_preTilt
-- name    : GroundTheory.PAdicHodge.nnnorm_algebraMap_preTilt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:41.991023+00:00
-- url     : https://prove2.me/theorems/c2713922-361c-4101-a394-bd1899433ee7
-- title:
--   PAdic Hodge: nnnorm algebra Map pre Tilt
-- statement:
--   The PAdic Hodge construction uses the nnnorm algebra Map pre Tilt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L142-L145

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

theorem GroundTheory.PAdicHodge.nnnorm_algebraMap_preTilt (a : 𝒪♭) : ‖algebraMap 𝒪♭ K♭ a‖₊ =
    PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p a := by sorry
