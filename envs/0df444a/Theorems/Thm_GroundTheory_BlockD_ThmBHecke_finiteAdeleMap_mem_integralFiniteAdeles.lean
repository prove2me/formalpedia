-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finiteAdeleMap_mem_integralFiniteAdeles
-- name    : GroundTheory.BlockD.ThmBHecke.finiteAdeleMap_mem_integralFiniteAdeles
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:54.82994+00:00
-- url     : https://prove2.me/theorems/d8614cd3-17c0-4364-af69-30e2e9c5d075
-- title:
--   Thm BHecke: finite Adele Map mem integral Finite Adeles
-- statement:
--   The Thm BHecke construction uses the finite Adele Map mem integral Finite Adeles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L103-L106

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

theorem GroundTheory.BlockD.ThmBHecke.finiteAdeleMap_mem_integralFiniteAdeles {a : Af F} (ha : a ∈ intAf F) :
    finiteAdeleMap F E a ∈ integralFiniteAdeles (𝓞 E) E := by sorry
