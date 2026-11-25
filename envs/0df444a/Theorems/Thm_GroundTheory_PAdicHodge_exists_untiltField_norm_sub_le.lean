-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_untiltField_norm_sub_le
-- name    : GroundTheory.PAdicHodge.exists_untiltField_norm_sub_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:46.738608+00:00
-- url     : https://prove2.me/theorems/e075a614-c03c-4a7a-b2cb-1fb129dc4fee
-- title:
--   PAdic Hodge: exists untilt Field norm sub le
-- statement:
--   The PAdic Hodge construction uses the exists untilt Field norm sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L54-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L54-L210

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
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
open Polynomial
variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
set_option synthInstance.maxHeartbeats 200000

theorem GroundTheory.PAdicHodge.exists_untiltField_norm_sub_le [IsAlgClosed C] [IsAlgClosed C♭]
    (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N]
    [FiniteDimensional K (untiltField K C p N)]
    (happrox : ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) {μ ε : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hμ : ‖(p : K)‖ ≤ μ ^ (minpoly K α).natDegree) (hε0 : 0 < ε) (hε1 : ε < 1)
    {β : C} (hβ : β ∈ untiltField K C p N) :
    ∃ N' : IntermediateField K♭ C♭, N ≤ N' ∧ FiniteDimensional K♭ N' ∧
      ∃ β' ∈ untiltField K C p N', ‖α - β'‖ ≤ μ / ε * ‖α - β‖ := by sorry
