-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_finiteCoord
-- name    : GroundTheory.Global.AdeleBaseChange.continuous_finiteCoord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:57:45.767926+00:00
-- url     : https://prove2.me/theorems/1daafdd5-9d0f-4279-bca0-bacee800e2ca
-- title:
--   Adele Base Change: continuous finite Coord
-- statement:
--   The Adele Base Change construction uses the continuous finite Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean#L46-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteTensor.lean#L46-L73

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
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
open IsDedekindDomain NumberField TensorProduct Module Filter Topology
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Global.AdeleBaseChange
open SemiLocal
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

theorem GroundTheory.Global.AdeleBaseChange.continuous_finiteCoord (i : ι) : Continuous (finiteCoord b i) := by sorry
