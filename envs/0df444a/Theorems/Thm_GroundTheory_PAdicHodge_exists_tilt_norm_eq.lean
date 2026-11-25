-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_tilt_norm_eq
-- name    : GroundTheory.PAdicHodge.exists_tilt_norm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:42.782814+00:00
-- url     : https://prove2.me/theorems/08008034-3434-4bc9-8742-7b918a250446
-- title:
--   PAdic Hodge: exists tilt norm eq
-- statement:
--   The PAdic Hodge construction uses the exists tilt norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L259-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/TiltField.lean#L259-L266

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

theorem GroundTheory.PAdicHodge.exists_tilt_norm_eq {y : K} (hy : y ≠ 0) : ∃ x : K♭, ‖x‖ = ‖y‖ := by sorry
