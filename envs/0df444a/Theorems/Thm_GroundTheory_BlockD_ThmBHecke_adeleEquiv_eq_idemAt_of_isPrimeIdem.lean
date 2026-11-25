-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_adeleEquiv_eq_idemAt_of_isPrimeIdem
-- name    : GroundTheory.BlockD.ThmBHecke.adeleEquiv_eq_idemAt_of_isPrimeIdem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:55:25.427598+00:00
-- url     : https://prove2.me/theorems/904552fa-133f-5fd4-8762-270f21df64ed
-- title:
--   Thm BHecke: adele Equiv eq idem At of is Prime Idem
-- statement:
--   The Thm BHecke construction uses the adele Equiv eq idem At of is Prime Idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L192-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L192-L199

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

theorem GroundTheory.BlockD.ThmBHecke.adeleEquiv_eq_idemAt_of_isPrimeIdem {σ : E →ₐ[F] E} {P : HeightOneSpectrum (𝓞 E)}
    {e f : AE F E} (h : IsPrimeIdem σ P e f) : adeleEquiv F E e = idemAt P := by sorry
