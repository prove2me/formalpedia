-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_char_iff_exists
-- name    : GroundTheory.BlockD.ThmBHecke.char_iff_exists
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:41:39.922445+00:00
-- url     : https://prove2.me/theorems/c4d1cb8f-0699-5757-a98d-1580292219fc
-- title:
--   Thm BHecke: char iff exists
-- statement:
--   The Thm BHecke construction uses the char iff exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L131-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L131-L148

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

theorem GroundTheory.BlockD.ThmBHecke.char_iff_exists {e : AE F E} (h01 : ∀ w, (adeleEquiv F E e).2 w = 0 ∨ (adeleEquiv F E e).2 w = 1)
    {x : 𝓞 E} (hx : x ≠ 0) :
    finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E ↔
      ∃ w, (adeleEquiv F E e).2 w = 1 ∧ x ∈ w.asIdeal := by sorry
