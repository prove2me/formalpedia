-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finSingleOne_of_ne
-- name    : GroundTheory.BlockD.ThmBHecke.finSingleOne_of_ne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:42:32.211947+00:00
-- url     : https://prove2.me/theorems/64dbe493-1726-4ce3-ad98-95f1d96ff845
-- title:
--   Thm BHecke: fin Single One of ne
-- statement:
--   The Thm BHecke construction uses the fin Single One of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L31-L33

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
variable {K : Type} [Field K] [NumberField K]

theorem GroundTheory.BlockD.ThmBHecke.finSingleOne_of_ne {w u : HeightOneSpectrum (𝓞 K)} (h : u ≠ w) : finSingleOne w u = 0 := by sorry
