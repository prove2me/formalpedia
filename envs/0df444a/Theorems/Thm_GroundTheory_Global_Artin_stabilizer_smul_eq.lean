-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_stabilizer_smul_eq
-- name    : GroundTheory.Global.Artin.stabilizer_smul_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:30:42.696658+00:00
-- url     : https://prove2.me/theorems/d1628047-2f59-4984-8008-9477f9dbe83e
-- title:
--   Artin: stabilizer smul eq
-- statement:
--   The Artin construction uses the stabilizer smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Places.lean#L114-L121

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

theorem GroundTheory.Global.Artin.stabilizer_smul_eq (x : Gal(L/K)) (P : Ideal (𝓞 L)) :
    MulAction.stabilizer H (x • P) =
      (MulAut.conj x • MulAction.stabilizer Gal(L/K) P : Subgroup Gal(L/K)).subgroupOf H := by sorry
