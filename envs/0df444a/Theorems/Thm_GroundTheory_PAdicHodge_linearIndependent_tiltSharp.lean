-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_linearIndependent_tiltSharp
-- name    : GroundTheory.PAdicHodge.linearIndependent_tiltSharp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:38.876857+00:00
-- url     : https://prove2.me/theorems/777fc4f0-add8-4926-9138-24ebe5b3821b
-- title:
--   PAdic Hodge: linear Independent tilt Sharp
-- statement:
--   The PAdic Hodge construction uses the linear Independent tilt Sharp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L152-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L152-L163

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

theorem GroundTheory.PAdicHodge.linearIndependent_tiltSharp {ι : Type*} [Fintype ι] {w : ι → C♭} {t r ρ : ℝ}
    (hw : ∀ (c : ι → K♭) (i : ι), t * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖)
    (hw1 : ∀ i, ‖w i‖ ≤ 1) (hwr : ∀ i, r < ‖w i‖) (ht : 0 < t) (hr : 0 < r) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hp : ‖(p : K)‖ ≤ t * r * ρ) :
    LinearIndependent K (fun i => tiltSharp C p (w i)) := by sorry
