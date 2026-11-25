-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_of_norm_sub_lt
-- name    : GroundTheory.PAdicHodge.norm_eq_of_norm_sub_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:47:51.267722+00:00
-- url     : https://prove2.me/theorems/e2c5b3ad-95e8-4761-96a1-6087367563f2
-- title:
--   PAdic Hodge: norm eq of norm sub lt
-- statement:
--   The PAdic Hodge construction uses the norm eq of norm sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UntiltIndep.lean#L37-L41

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
omit [NontriviallyNormedField K] [IsUltrametricDist K] [NontriviallyNormedField C] [NormedAlgebra K C]
  [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

theorem GroundTheory.PAdicHodge.norm_eq_of_norm_sub_lt {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖x - y‖ < ‖y‖) : ‖x‖ = ‖y‖ := by sorry
