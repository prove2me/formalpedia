-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_exists_mem_not_mem
-- name    : GroundTheory.BlockD.ThmBHecke.exists_mem_not_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:42:16.485208+00:00
-- url     : https://prove2.me/theorems/fa5dcd87-5507-5abb-8485-49f33815f588
-- title:
--   Thm BHecke: exists mem not mem
-- statement:
--   The Thm BHecke construction uses the exists mem not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L150-L154

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

theorem GroundTheory.BlockD.ThmBHecke.exists_mem_not_mem {P w : HeightOneSpectrum (𝓞 E)} (h : w ≠ P) :
    ∃ x : 𝓞 E, x ∈ w.asIdeal ∧ x ∉ P.asIdeal := by sorry
