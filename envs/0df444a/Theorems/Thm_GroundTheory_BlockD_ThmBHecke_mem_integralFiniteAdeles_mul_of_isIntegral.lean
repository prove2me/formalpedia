-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_mem_integralFiniteAdeles_mul_of_isIntegral
-- name    : GroundTheory.BlockD.ThmBHecke.mem_integralFiniteAdeles_mul_of_isIntegral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:28.175567+00:00
-- url     : https://prove2.me/theorems/5da82a8b-d55e-505b-907d-dacf2da4a7fc
-- title:
--   Thm BHecke: mem integral Finite Adeles mul of is Integral
-- statement:
--   The Thm BHecke construction uses the mem integral Finite Adeles mul of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L131-L134

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteTensor
import Definitions.Def_GroundTheory_IdeleRoots_TorusPowers_HeckeTensor
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
open GroundTheory GroundTheory.BlockD
open GroundTheory.BlockD.ThmBHecke
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GroundTheory.BlockD.ThmBHecke.mem_integralFiniteAdeles_mul_of_isIntegral {s : FiniteAdeleRing (𝓞 E) E}
    (hs : s ∈ integralFiniteAdeles (𝓞 E) E) {x : E} (hx : IsIntegral ℤ x) (w : HeightOneSpectrum (𝓞 E)) :
    s w * algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E := by sorry
