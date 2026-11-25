-- Prove2me | Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul_snd
-- name    : GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_tmul_snd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:00:39.893216+00:00
-- url     : https://prove2.me/theorems/930f0c8a-5050-46c2-bdfa-954ec26058cb
-- title:
--   Adele Base Change: adele Tensor Equiv tmul snd
-- statement:
--   The Adele Base Change construction uses the adele Tensor Equiv tmul snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/BaseChange/AdeleEquiv.lean#L47-L50

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

theorem GroundTheory.Global.AdeleBaseChange.adeleTensorEquiv_tmul_snd (l : L) (a : 𝔸[K]) (w : HeightOneSpectrum (𝓞 L)) :
    (adeleTensorEquiv K L (l ⊗ₜ a)).2 w =
      SemiLocal.tensorEquiv' L (below K w) (l ⊗ₜ a.2 (below K w)) ⟨w, liesOver_below w⟩ := by sorry
