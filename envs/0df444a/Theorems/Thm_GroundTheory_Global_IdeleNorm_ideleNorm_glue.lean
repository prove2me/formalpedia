-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleNorm_ideleNorm_glue
-- name    : GroundTheory.Global.IdeleNorm.ideleNorm_glue
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:52:04.10589+00:00
-- url     : https://prove2.me/theorems/4fa06657-5631-43e0-b0fe-aebef352c711
-- title:
--   Idele Norm: idele Norm glue
-- statement:
--   The Idele Norm construction uses the idele Norm glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L156-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalNorms.lean#L156-L169

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_CompletionsOverBasisRepr
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange_FiniteMap
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing NumberField.LiesOver
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L]
  [Algebra K L]
variable {L}

theorem GroundTheory.Global.IdeleNorm.ideleNorm_glue (yf : ∀ v : HeightOneSpectrum (𝓞 K),
      (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ)
    (hyf : ∀ᶠ v in cofinite, yf v ∈ integerUnitsOver L v)
    (yi : ∀ v : InfinitePlace K, (w : v.placesOver L) → ((w : InfinitePlace L).Completion)ˣ)
    {x : IdeleGroup K} (hf : ∀ v, finiteLocalNorm L v (yf v) = IdeleGroup.finiteProj v x)
    (hi : ∀ v, infiniteLocalNorm L v (yi v) = IdeleGroup.infiniteProj v x) :
    ideleNorm K L (glue yf hyf yi) = x := by sorry
