-- Prove2me | Theorems.Thm_GroundTheory_Global_coeff_map_C_mul_matrixGeomSeries
-- name    : GroundTheory.Global.coeff_map_C_mul_matrixGeomSeries
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:14.062352+00:00
-- url     : https://prove2.me/theorems/cde57700-3064-491b-a216-734abfe1afc2
-- title:
--   Global: coeff map C mul matrix Geom Series
-- statement:
--   The Global construction uses the coeff map C mul matrix Geom Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L16-L20

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem GroundTheory.Global.coeff_map_C_mul_matrixGeomSeries (M : Matrix n n R) (k : ℕ) (i j : n) :
    PowerSeries.coeff k ((M.map PowerSeries.C * matrixGeomSeries M) i j) = (M ^ (k + 1)) i j := by sorry
