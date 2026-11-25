-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_orthogonal_normalized
-- name    : GroundTheory.PAdicHodge.exists_orthogonal_normalized
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:57.627508+00:00
-- url     : https://prove2.me/theorems/fb01d6b2-f5d3-4fb3-ad21-b34ef3d246b6
-- title:
--   PAdic Hodge: exists orthogonal normalized
-- statement:
--   The PAdic Hodge construction uses the exists orthogonal normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L165-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L165-L192

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

theorem GroundTheory.PAdicHodge.exists_orthogonal_normalized {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) {t r : ℝ} (ht : t < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ w : ι → C♭, LinearIndependent K♭ w ∧ (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧
      (∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖) ∧
      ∀ i, ‖w i‖ ≤ 1 ∧ r < ‖w i‖ := by sorry
