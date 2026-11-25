-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_cA_algebraMap
-- name    : GroundTheory.BlockD.ThmBHecke.cA_algebraMap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:40.442797+00:00
-- url     : https://prove2.me/theorems/9838c709-c5e8-4e2f-8d8d-3b006f2ca17b
-- title:
--   Thm BHecke: c A algebra Map
-- statement:
--   The Thm BHecke construction uses the c A algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L227-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L227-L229

import Mathlib
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E}

theorem GroundTheory.BlockD.ThmBHecke.cA_algebraMap (a : AF F) :
    cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := by sorry
