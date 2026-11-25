-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_IsCMExt_sigma_sigma
-- name    : GroundTheory.BlockD.ThmBHecke.IsCMExt.sigma_sigma
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:41:21.536282+00:00
-- url     : https://prove2.me/theorems/a0030792-224d-5716-b02e-5d9f2119dea7
-- title:
--   Is CMExt: sigma sigma
-- statement:
--   The Is CMExt construction uses the sigma sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L233-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L233-L236

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

theorem GroundTheory.BlockD.ThmBHecke.IsCMExt.sigma_sigma (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by sorry
