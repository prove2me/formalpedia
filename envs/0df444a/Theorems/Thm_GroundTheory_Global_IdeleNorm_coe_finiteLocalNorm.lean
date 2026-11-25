-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_coe_finiteLocalNorm
-- name    : GroundTheory.Global.IdeleNorm.coe_finiteLocalNorm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:56:46.027895+00:00
-- url     : https://prove2.me/theorems/0a5e2fe8-dd75-5bc2-8619-19a1938d7c33
-- title:
--   Idele Norm: coe finite Local Norm
-- statement:
--   The Idele Norm construction uses the coe finite Local Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L28-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}

theorem GroundTheory.Global.IdeleNorm.coe_finiteLocalNorm (v : HeightOneSpectrum (𝓞 K))
    (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    ((finiteLocalNorm L v y : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ∏ w, Algebra.norm (v.adicCompletion K) (y w : w.1.adicCompletion L) := by sorry
