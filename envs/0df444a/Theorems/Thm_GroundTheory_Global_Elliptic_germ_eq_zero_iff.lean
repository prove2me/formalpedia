-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_germ_eq_zero_iff
-- name    : GroundTheory.Global.Elliptic.germ_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:57.122209+00:00
-- url     : https://prove2.me/theorems/164d19b8-f14c-49c0-a3c0-278e16c6adbf
-- title:
--   Elliptic: germ eq zero iff
-- statement:
--   The Elliptic construction uses the germ eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AnalyticAlgebraicGerm.lean#L124-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/AnalyticAlgebraicGerm.lean#L124-L125

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem GroundTheory.Global.Elliptic.germ_eq_zero_iff {f : ℂ → ℂ} (hf : Meromorphic f) : germ f = 0 ↔ f =ᶠ[codiscrete ℂ] 0 := by sorry
