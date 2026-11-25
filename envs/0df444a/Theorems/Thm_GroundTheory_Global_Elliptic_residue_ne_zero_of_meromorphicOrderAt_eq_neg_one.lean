-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_residue_ne_zero_of_meromorphicOrderAt_eq_neg_one
-- name    : GroundTheory.Global.Elliptic.residue_ne_zero_of_meromorphicOrderAt_eq_neg_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:44.886205+00:00
-- url     : https://prove2.me/theorems/9def3a6e-f888-4b80-b953-f8189458fe03
-- title:
--   Elliptic: residue ne zero of meromorphic Order At eq neg one
-- statement:
--   The Elliptic construction uses the residue ne zero of meromorphic Order At eq neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L304-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L304-L319

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

theorem GroundTheory.Global.Elliptic.residue_ne_zero_of_meromorphicOrderAt_eq_neg_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (h : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ)) :
    residue f p ≠ 0 := by sorry
