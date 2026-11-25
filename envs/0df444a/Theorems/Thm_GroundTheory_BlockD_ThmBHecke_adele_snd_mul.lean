-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_adele_snd_mul
-- name    : GroundTheory.BlockD.ThmBHecke.adele_snd_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:01.50883+00:00
-- url     : https://prove2.me/theorems/b60b9b92-d033-571f-be07-c74e23bbb9ad
-- title:
--   Thm BHecke: adele snd mul
-- statement:
--   The Thm BHecke construction uses the adele snd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L66-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L66-L66

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

theorem GroundTheory.BlockD.ThmBHecke.adele_snd_mul (a b : 𝔸[E]) (w : HeightOneSpectrum (𝓞 E)) : (a * b).2 w = a.2 w * b.2 w := by sorry
