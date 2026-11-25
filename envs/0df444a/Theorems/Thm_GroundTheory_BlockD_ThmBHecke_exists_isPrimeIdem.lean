-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_exists_isPrimeIdem
-- name    : GroundTheory.BlockD.ThmBHecke.exists_isPrimeIdem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:39.535821+00:00
-- url     : https://prove2.me/theorems/537aafa1-203f-511c-a490-9c0f156e5987
-- title:
--   Thm BHecke: exists is Prime Idem
-- statement:
--   The Thm BHecke construction uses the exists is Prime Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L321-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L321-L422

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

theorem GroundTheory.BlockD.ThmBHecke.exists_isPrimeIdem {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ f, IsPrimeIdem σ P ((adeleEquiv F E).symm (idemAt P)) f := by sorry
