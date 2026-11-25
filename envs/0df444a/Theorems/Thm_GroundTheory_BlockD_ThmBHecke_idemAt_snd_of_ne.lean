-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_idemAt_snd_of_ne
-- name    : GroundTheory.BlockD.ThmBHecke.idemAt_snd_of_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:54.495499+00:00
-- url     : https://prove2.me/theorems/5c661e8e-342c-5216-b58e-ad6406e026eb
-- title:
--   Thm BHecke: idem At snd of ne
-- statement:
--   The Thm BHecke construction uses the idem At snd of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L53-L54

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

theorem GroundTheory.BlockD.ThmBHecke.idemAt_snd_of_ne {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) : (idemAt P).2 w = 0 := by sorry
