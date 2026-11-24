-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_tiltSharp_linearIndependent
-- name    : GroundTheory.PAdicHodge.exists_tiltSharp_linearIndependent
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:38.145889+00:00
-- url     : https://prove2.me/theorems/001799b1-b2ad-4cbb-998c-d12bafa087bc
-- title:
--   PAdic Hodge: exists tilt Sharp linear Independent
-- statement:
--   The PAdic Hodge construction uses the exists tilt Sharp linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L209-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L209-L217

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

theorem GroundTheory.PAdicHodge.exists_tiltSharp_linearIndependent {ι : Type*} [Fintype ι] {v : ι → C♭}
    (hv : LinearIndependent K♭ v) :
    ∃ w : ι → C♭, (∀ i, w i ∈ Submodule.span K♭ (Set.range v)) ∧ (∀ i, ‖w i‖ ≤ 1) ∧
      LinearIndependent K♭ w ∧ LinearIndependent K (fun i => tiltSharp C p (w i)) := by sorry
