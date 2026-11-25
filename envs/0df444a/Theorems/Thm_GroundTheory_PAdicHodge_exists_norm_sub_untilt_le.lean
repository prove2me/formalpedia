-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_norm_sub_untilt_le
-- name    : GroundTheory.PAdicHodge.exists_norm_sub_untilt_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:38:48.610898+00:00
-- url     : https://prove2.me/theorems/9df88d62-6410-4ec7-bff3-33c662df068d
-- title:
--   PAdic Hodge: exists norm sub untilt le
-- statement:
--   The PAdic Hodge construction uses the exists norm sub untilt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L236-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltPerfectoid.lean#L236-L256

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

theorem GroundTheory.PAdicHodge.exists_norm_sub_untilt_le (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] {y : C}
    (hy : y ∈ untiltField K C p N) (hy1 : ‖y‖ ≤ 1) :
    ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by sorry
