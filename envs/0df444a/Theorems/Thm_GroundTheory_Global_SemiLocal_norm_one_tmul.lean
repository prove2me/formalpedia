-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_norm_one_tmul
-- name    : GroundTheory.Global.SemiLocal.norm_one_tmul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:13:35.048987+00:00
-- url     : https://prove2.me/theorems/ea82ec06-a62a-5b17-90ba-7cc8e1255231
-- title:
--   Semi Local: norm one tmul
-- statement:
--   The Semi Local construction uses the norm one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L58-L61

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
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
open IsDedekindDomain NumberField TensorProduct Module Matrix
noncomputable section
open GroundTheory.Global.SemiLocal
variable {R : Type*} [Field R] {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, CommRing (S i)]
  [∀ i, Algebra R (S i)] [∀ i, Module.Finite R (S i)]
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.SemiLocal.norm_one_tmul (x : L) :
    Algebra.norm (v.adicCompletion K) ((1 : v.adicCompletion K) ⊗ₜ[K] x) =
      algebraMap K (v.adicCompletion K) (Algebra.norm K x) := by sorry
