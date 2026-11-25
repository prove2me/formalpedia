-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_mem_untiltField_of_approx
-- name    : GroundTheory.PAdicHodge.exists_mem_untiltField_of_approx
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:25.537037+00:00
-- url     : https://prove2.me/theorems/60f31795-64c0-5ad1-991a-e3d12be5469e
-- title:
--   PAdic Hodge: exists mem untilt Field of approx
-- statement:
--   The PAdic Hodge construction uses the exists mem untilt Field of approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L212-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltApprox.lean#L212-L288

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

theorem GroundTheory.PAdicHodge.exists_mem_untiltField_of_approx [IsAlgClosed C] [IsAlgClosed C♭]
    (hfin : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      FiniteDimensional K (untiltField K C p N))
    (happrox : ∀ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N →
      ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
        ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖)
    {α : C} (hα : IsIntegral K α) :
    ∃ N : IntermediateField K♭ C♭, FiniteDimensional K♭ N ∧ α ∈ untiltField K C p N := by sorry
