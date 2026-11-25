-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_symm_apply
-- name    : GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_symm_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:49:07.243809+00:00
-- url     : https://prove2.me/theorems/da48a841-d55b-43a9-93e4-8e2855b9c74f
-- title:
--   Adele Base Change: adele Tensor Equiv symm apply
-- statement:
--   The Adele Base Change construction uses the adele Tensor Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L89-L92

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

theorem GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_symm_apply (y : 𝔸[L]) :
    (adeleTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ coord b i y := by sorry
