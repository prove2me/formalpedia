-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_coe_ideleEquiv
-- name    : GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:17.437455+00:00
-- url     : https://prove2.me/theorems/81191dc4-3fa4-5e68-8b18-8e1a0df448bd
-- title:
--   Thm BHecke: coe idele Equiv
-- statement:
--   The Thm BHecke construction uses the coe idele Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L52-L53

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

theorem GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv (x : (AE F E)ˣ) : ((ideleEquiv F E x : IdeleGroup E) : 𝔸[E]) = adeleEquiv F E x := by sorry

attribute [defeq] GroundTheory.BlockD.ThmBHecke.coe_ideleEquiv
