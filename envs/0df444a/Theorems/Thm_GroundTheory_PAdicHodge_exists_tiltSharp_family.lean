-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_tiltSharp_family
-- name    : GroundTheory.PAdicHodge.exists_tiltSharp_family
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:53.386974+00:00
-- url     : https://prove2.me/theorems/ee901011-55ff-4242-af11-37bbccbdee47
-- title:
--   PAdic Hodge: exists tilt Sharp family
-- statement:
--   The PAdic Hodge construction uses the exists tilt Sharp family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L194-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L194-L207

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Definitions.Def_GroundTheory_PAdicHodge_UntiltIndep
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

theorem GroundTheory.PAdicHodge.exists_tiltSharp_family {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ (w : ι → C♭) (t r ρ : ℝ), 0 < t ∧ t < 1 ∧ 0 < r ∧ r < 1 ∧ 0 < ρ ∧ ρ < 1 ∧
      ‖(p : K)‖ ≤ t * r * ρ ∧ LinearIndependent K♭ w ∧
      (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      (∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖) ∧
      ∀ (l : ι → K) (i : ι), t * r * ρ * ‖l i‖ ≤ ‖∑ j, l j • tiltSharp C p (w j)‖ := by sorry
