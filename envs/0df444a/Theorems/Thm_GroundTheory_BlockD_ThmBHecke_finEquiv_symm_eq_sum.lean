-- Prove2me | Theorems.Thm_GroundTheory_BlockD_ThmBHecke_finEquiv_symm_eq_sum
-- name    : GroundTheory.BlockD.ThmBHecke.finEquiv_symm_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:06.769149+00:00
-- url     : https://prove2.me/theorems/80dc234f-e4d3-5906-9734-46f5afbd28b1
-- title:
--   Thm BHecke: fin Equiv symm eq sum
-- statement:
--   The Thm BHecke construction uses the fin Equiv symm eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/IdeleRoots/TorusPowers/HeckeTensor.lean#L92-L97

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

theorem GroundTheory.BlockD.ThmBHecke.finEquiv_symm_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (t : FiniteAdeleRing (𝓞 E) E) :
    (finEquiv F E).symm t = ∑ i, finiteCoord b i t ⊗ₜ b i := by sorry
