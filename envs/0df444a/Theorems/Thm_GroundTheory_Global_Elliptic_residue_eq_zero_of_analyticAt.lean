-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_residue_eq_zero_of_analyticAt
-- name    : GroundTheory.Global.Elliptic.residue_eq_zero_of_analyticAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:26.730638+00:00
-- url     : https://prove2.me/theorems/855e14fc-6d7a-4c4a-99ed-702ce3157cc6
-- title:
--   Elliptic: residue eq zero of analytic At
-- statement:
--   The Elliptic construction uses the residue eq zero of analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L223-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L223-L225

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

theorem GroundTheory.Global.Elliptic.residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    residue f p = 0 := by sorry
