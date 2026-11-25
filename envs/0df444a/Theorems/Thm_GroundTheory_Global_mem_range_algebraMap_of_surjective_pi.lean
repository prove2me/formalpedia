-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_range_algebraMap_of_surjective_pi
-- name    : GroundTheory.Global.mem_range_algebraMap_of_surjective_pi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:22.023541+00:00
-- url     : https://prove2.me/theorems/5b7e9ba6-2143-4a45-bdd2-32a6f89cf326
-- title:
--   Global: mem range algebra Map of surjective pi
-- statement:
--   The Global construction uses the mem range algebra Map of surjective pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/Splitting.lean#L16-L27

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem GroundTheory.Global.mem_range_algebraMap_of_surjective_pi {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) (e : E) :
    e ∈ Set.range (algebraMap F E) := by sorry
