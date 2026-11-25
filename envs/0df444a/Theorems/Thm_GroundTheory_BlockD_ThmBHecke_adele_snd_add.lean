-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_adele_snd_add
-- name    : GroundTheory.BlockD.ThmBHecke.adele_snd_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:49.407683+00:00
-- url     : https://prove2.me/theorems/a03c01b9-6f7c-4238-84e6-4b2b2f1f8d58
-- title:
--   Thm BHecke: adele snd add
-- statement:
--   The Thm BHecke construction uses the adele snd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L70-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L70-L70

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

theorem GroundTheory.BlockD.ThmBHecke.adele_snd_add (a b : 𝔸[E]) (w : HeightOneSpectrum (𝓞 E)) : (a + b).2 w = a.2 w + b.2 w := by sorry
