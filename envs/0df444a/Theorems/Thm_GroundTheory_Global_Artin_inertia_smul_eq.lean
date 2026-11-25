-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_inertia_smul_eq
-- name    : GroundTheory.Global.Artin.inertia_smul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:59.741643+00:00
-- url     : https://prove2.me/theorems/d595bff2-5a40-475b-a124-91ab709f9474
-- title:
--   Artin: inertia smul eq
-- statement:
--   The Artin construction uses the inertia smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean#L125-L129

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobeniusEmbed
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
omit [NumberField K] [NumberField L] [IsGalois K L]

theorem GroundTheory.Global.Artin.inertia_smul_eq (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    (x • P).inertia H =
      (MulAut.conj x • P.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H := by sorry
