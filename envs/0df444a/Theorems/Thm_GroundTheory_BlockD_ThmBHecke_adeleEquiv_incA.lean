-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_adeleEquiv_incA
-- name    : GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:12.90695+00:00
-- url     : https://prove2.me/theorems/00187d26-bf1f-4b9e-89b0-30e954080c70
-- title:
--   Thm BHecke: adele Equiv inc A
-- statement:
--   The Thm BHecke construction uses the adele Equiv inc A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L27-L29

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

theorem GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (x : E) : adeleEquiv F E (incA F E x) = algebraMap E 𝔸[E] x := by sorry
