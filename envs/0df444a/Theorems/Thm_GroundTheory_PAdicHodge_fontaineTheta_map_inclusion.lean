-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_fontaineTheta_map_inclusion
-- name    : GroundTheory.PAdicHodge.fontaineTheta_map_inclusion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:30.448141+00:00
-- url     : https://prove2.me/theorems/1094064c-7372-4cd8-b00e-32fac04121bd
-- title:
--   PAdic Hodge: fontaine Theta map inclusion
-- statement:
--   The PAdic Hodge construction uses the fontaine Theta map inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWNatural.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Definitions.Def_GroundTheory_PAdicHodge_FWNatural
import Theorems.Thm_GroundTheory_PAdicHodge_integerTilt_mono

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

theorem GroundTheory.PAdicHodge.fontaineTheta_map_inclusion {N N' : IntermediateField K♭ C♭} (h : N ≤ N')
    (u : WittVector p (integerTilt K C p N)) :
    θ (WittVector.map (integerTilt K C p N').subtype
        (WittVector.map (Subring.inclusion (integerTilt_mono h)) u)) =
      θ (WittVector.map (integerTilt K C p N).subtype u) := by sorry
