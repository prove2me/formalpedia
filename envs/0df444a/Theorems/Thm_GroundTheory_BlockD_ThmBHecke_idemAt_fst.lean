-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_idemAt_fst
-- name    : GroundTheory.BlockD.ThmBHecke.idemAt_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:44:19.909044+00:00
-- url     : https://prove2.me/theorems/e83ae5e2-74cf-4fc1-ae3c-99fcf24e5324
-- title:
--   Thm BHecke: idem At fst
-- statement:
--   The Thm BHecke construction uses the idem At fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L48-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L48-L48

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

theorem GroundTheory.BlockD.ThmBHecke.idemAt_fst (P : HeightOneSpectrum (𝓞 E)) : (idemAt P).1 = 0 := by sorry

attribute [defeq] GroundTheory.BlockD.ThmBHecke.idemAt_fst
