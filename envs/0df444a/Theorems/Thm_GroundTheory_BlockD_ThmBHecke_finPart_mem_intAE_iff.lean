-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finPart_mem_intAE_iff
-- name    : GroundTheory.BlockD.ThmBHecke.finPart_mem_intAE_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:39.611643+00:00
-- url     : https://prove2.me/theorems/7e114687-a7b6-52d9-877d-e81c0af52104
-- title:
--   Thm BHecke: fin Part mem int AE iff
-- statement:
--   The Thm BHecke construction uses the fin Part mem int AE iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L110-L113

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

theorem GroundTheory.BlockD.ThmBHecke.finPart_mem_intAE_iff (z : AE F E) :
    finPart F E z ∈ intAE F E ↔ ∀ w, (adeleEquiv F E z).2 w ∈ w.adicCompletionIntegers E := by sorry
