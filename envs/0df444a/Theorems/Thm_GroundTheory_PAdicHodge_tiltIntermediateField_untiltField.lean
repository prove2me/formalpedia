-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_tiltIntermediateField_untiltField
-- name    : GroundTheory.PAdicHodge.tiltIntermediateField_untiltField
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:46.687418+00:00
-- url     : https://prove2.me/theorems/1d3cd2d8-2662-5817-a887-9cf3d22f1547
-- title:
--   PAdic Hodge: tilt Intermediate Field untilt Field
-- statement:
--   The PAdic Hodge construction uses the tilt Intermediate Field untilt Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L206-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L206-L234

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

theorem GroundTheory.PAdicHodge.tiltIntermediateField_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    tiltIntermediateField p (untiltField K C p N) = N := by sorry
