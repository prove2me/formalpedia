-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_le_tiltIntermediateField_untiltField
-- name    : GroundTheory.PAdicHodge.le_tiltIntermediateField_untiltField
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:26.3424+00:00
-- url     : https://prove2.me/theorems/ad2574c4-a95d-4087-a9ef-ce0a314eeb58
-- title:
--   PAdic Hodge: le tilt Intermediate Field untilt Field
-- statement:
--   The PAdic Hodge construction uses the le tilt Intermediate Field untilt Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L191-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L191-L204

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltDegree
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
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
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

theorem GroundTheory.PAdicHodge.le_tiltIntermediateField_untiltField (N : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ N] : N ≤ tiltIntermediateField p (untiltField K C p N) := by sorry
