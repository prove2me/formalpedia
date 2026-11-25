-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_eq_principalPart_add_regularPart
-- name    : GroundTheory.Global.Elliptic.eq_principalPart_add_regularPart
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:58.456598+00:00
-- url     : https://prove2.me/theorems/2149b906-4e14-4130-afec-acedc08e25d9
-- title:
--   Elliptic: eq principal Part add regular Part
-- statement:
--   The Elliptic construction uses the eq principal Part add regular Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L143-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L143-L161

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem GroundTheory.Global.Elliptic.eq_principalPart_add_regularPart (f : ℂ → ℂ) (p : ℂ) {z : ℂ} (hz : z ≠ p) :
    f z = principalPart f p z + regularPart f p z := by sorry
