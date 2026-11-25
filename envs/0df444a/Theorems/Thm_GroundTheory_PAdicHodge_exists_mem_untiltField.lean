-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_mem_untiltField
-- name    : GroundTheory.PAdicHodge.exists_mem_untiltField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:44.955007+00:00
-- url     : https://prove2.me/theorems/55fba047-b456-4421-b4ff-1a67f53703c2
-- title:
--   PAdic Hodge: exists mem untilt Field
-- statement:
--   The PAdic Hodge construction uses the exists mem untilt Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L308-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L308-L311

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

theorem GroundTheory.PAdicHodge.exists_mem_untiltField [IsAlgClosed C] {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N := by sorry
