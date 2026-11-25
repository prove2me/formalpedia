-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_continuous_localCoord
-- name    : GroundTheory.Global.AdeleBaseChange.continuous_localCoord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:13.403209+00:00
-- url     : https://prove2.me/theorems/20abdf7f-6bd0-43b1-8edb-50b74aab6c3a
-- title:
--   Adele Base Change: continuous local Coord
-- statement:
--   The Adele Base Change construction uses the continuous local Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean#L101-L103

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteCoord
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
omit [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Global.AdeleBaseChange.continuous_localCoord (v : HeightOneSpectrum (𝓞 K)) (i : ι) :
    Continuous (localCoord b v i) := by sorry
