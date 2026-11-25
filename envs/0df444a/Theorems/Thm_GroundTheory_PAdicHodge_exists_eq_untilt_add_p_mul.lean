-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_untilt_add_p_mul
-- name    : GroundTheory.PAdicHodge.exists_eq_untilt_add_p_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:33.939243+00:00
-- url     : https://prove2.me/theorems/ab9d80ef-d4bd-4bd8-8a8f-ab2fa5d09802
-- title:
--   PAdic Hodge: exists eq untilt add p mul
-- statement:
--   The PAdic Hodge construction uses the exists eq untilt add p mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L87-L105

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_UntiltField
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
local notation "𝒪C♭" => PreTilt (normInteger C) p
local notation "θ" => WittVector.fontaineTheta (normInteger C) p

theorem GroundTheory.PAdicHodge.exists_eq_untilt_add_p_mul {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N]
    {z : normInteger C} (hz : z ∈ untiltInteger K C p N) :
    ∃ a ∈ integerTilt K C p N, ∃ z' ∈ untiltInteger K C p N,
      z = PreTilt.untilt a + (p : normInteger C) * z' := by sorry
