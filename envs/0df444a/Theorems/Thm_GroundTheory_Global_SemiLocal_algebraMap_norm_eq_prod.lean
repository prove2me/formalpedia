-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_algebraMap_norm_eq_prod
-- name    : GroundTheory.Global.SemiLocal.algebraMap_norm_eq_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:35.938696+00:00
-- url     : https://prove2.me/theorems/b74e152c-ecbd-5aa6-924c-455eb55e98b9
-- title:
--   Semi Local: algebra Map norm eq prod
-- statement:
--   The Semi Local construction uses the algebra Map norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/NormTrace.lean#L70-L76

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

theorem GroundTheory.Global.SemiLocal.algebraMap_norm_eq_prod (x : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K x) =
      ∏ w : PlacesOver L v,
        Algebra.norm (v.adicCompletion K) (algebraMap L (w.1.adicCompletion L) x) := by sorry
