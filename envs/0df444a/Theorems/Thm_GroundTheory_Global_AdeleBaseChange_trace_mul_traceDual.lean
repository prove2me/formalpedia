-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_trace_mul_traceDual
-- name    : GroundTheory.Global.AdeleBaseChange.trace_mul_traceDual
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:00.298478+00:00
-- url     : https://prove2.me/theorems/97ee6b5a-5612-56d1-8c1a-29f4437628e7
-- title:
--   Adele Base Change: trace mul trace Dual
-- statement:
--   The Adele Base Change construction uses the trace mul trace Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/FiniteCoord.lean#L35-L38

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

theorem GroundTheory.Global.AdeleBaseChange.trace_mul_traceDual (i j : ι) :
    Algebra.trace K L (b j * traceDual b i) = if j = i then 1 else 0 := by sorry
