-- Prove2me | Theorems.Thm_GroundTheory_Global_fourierChar_add_intCast
-- name    : GroundTheory.Global.fourierChar_add_intCast
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:53.725268+00:00
-- url     : https://prove2.me/theorems/740327a8-1255-4cb5-89f6-f8a1fd6956ca
-- title:
--   Global: fourier Char add int Cast
-- statement:
--   The Global construction uses the fourier Char add int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section

theorem GroundTheory.Global.fourierChar_add_intCast (x : ℝ) (k : ℤ) : 𝐞 (x + k) = 𝐞 x := by sorry
