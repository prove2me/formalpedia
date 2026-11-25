-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul
-- name    : GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_tmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:24.97687+00:00
-- url     : https://prove2.me/theorems/9a722251-ddb2-4a2c-8cba-1796e1189b1a
-- title:
--   Adele Base Change: adele Tensor Equiv tmul
-- statement:
--   The Adele Base Change construction uses the adele Tensor Equiv tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L42-L45

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_InfiniteAdeleTopology
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_AdeleEquiv
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
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_tmul (l : L) (a : 𝔸[K]) :
    adeleTensorEquiv K L (l ⊗ₜ a) = algebraMap L 𝔸[L] l * adeleMap K L a := by sorry
