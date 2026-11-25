-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_untilt_sum_eq
-- name    : GroundTheory.PAdicHodge.exists_untilt_sum_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:08.586988+00:00
-- url     : https://prove2.me/theorems/60d0bac6-a99f-443d-9346-b723fe5f741b
-- title:
--   PAdic Hodge: exists untilt sum eq
-- statement:
--   The PAdic Hodge construction uses the exists untilt sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L107-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltField.lean#L107-L133

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

theorem GroundTheory.PAdicHodge.exists_untilt_sum_eq {N : IntermediateField K♭ C♭} [FiniteDimensional K♭ N] {ι : Type*}
    (s : Finset ι) (a : ι → integerTilt K C p N) :
    ∃ z ∈ untiltInteger K C p N, PreTilt.untilt (∑ i ∈ s, (a i : 𝒪C♭)) =
      ∑ i ∈ s, PreTilt.untilt (a i : 𝒪C♭) + (p : normInteger C) * z := by sorry
