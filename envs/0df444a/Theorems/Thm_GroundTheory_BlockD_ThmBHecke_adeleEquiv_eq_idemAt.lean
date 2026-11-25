-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_adeleEquiv_eq_idemAt
-- name    : GroundTheory.BlockD.ThmBHecke.adeleEquiv_eq_idemAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:44:12.288792+00:00
-- url     : https://prove2.me/theorems/f055571e-78d1-40c4-80bc-7ba0927f82d8
-- title:
--   Thm BHecke: adele Equiv eq idem At
-- statement:
--   The Thm BHecke construction uses the adele Equiv eq idem At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L156-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeIdem.lean#L156-L190

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

theorem GroundTheory.BlockD.ThmBHecke.adeleEquiv_eq_idemAt {e : AE F E} {P : HeightOneSpectrum (𝓞 E)} (he : e * e = e)
    {v : HeightOneSpectrum (𝓞 F)} {ε : AF F} (hε : IsPlaceIdem F v ε)
    (hee : e * algebraMap (AF F) (AE F E) ε = e)
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart F E (e * incA F E ((x : E)⁻¹)) ∉ intAE F E)) :
    adeleEquiv F E e = idemAt P := by sorry
