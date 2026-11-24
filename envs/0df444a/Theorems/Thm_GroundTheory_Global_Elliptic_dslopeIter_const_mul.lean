-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_dslopeIter_const_mul
-- name    : GroundTheory.Global.Elliptic.dslopeIter_const_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:38:50.756114+00:00
-- url     : https://prove2.me/theorems/6f53afb9-f9d0-481f-b826-3038e93eaf09
-- title:
--   Elliptic: dslope Iter const mul
-- statement:
--   The Elliptic construction uses the dslope Iter const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L67-L72

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

theorem GroundTheory.Global.Elliptic.dslopeIter_const_mul (p a : ℂ) (g : ℂ → ℂ) (k : ℕ) :
    dslopeIter p k (fun z ↦ a * g z) = fun z ↦ a * dslopeIter p k g z := by sorry
