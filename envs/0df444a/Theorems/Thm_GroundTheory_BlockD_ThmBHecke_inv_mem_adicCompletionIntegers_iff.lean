-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_inv_mem_adicCompletionIntegers_iff
-- name    : GroundTheory.BlockD.ThmBHecke.inv_mem_adicCompletionIntegers_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:24.154923+00:00
-- url     : https://prove2.me/theorems/191fada7-0d05-5925-9019-01f79b0a49be
-- title:
--   Thm BHecke: inv mem adic Completion Integers iff
-- statement:
--   The Thm BHecke construction uses the inv mem adic Completion Integers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L121-L129

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

theorem GroundTheory.BlockD.ThmBHecke.inv_mem_adicCompletionIntegers_iff (w : HeightOneSpectrum (𝓞 E)) {x : 𝓞 E} (hx : x ≠ 0) :
    algebraMap E (w.adicCompletion E) ((x : E)⁻¹) ∈ w.adicCompletionIntegers E ↔ x ∉ w.asIdeal := by sorry
