-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_OpenLat_nsmul_integral_mem_nhds
-- name    : GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:53.936008+00:00
-- url     : https://prove2.me/theorems/7a82e547-caf5-4157-b728-c1b780151058
-- title:
--   Open Lat: nsmul integral mem nhds
-- statement:
--   The Open Lat construction uses the nsmul integral mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean#L35-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.OpenLat
variable (F : Type) [Field F] [NumberField F]

theorem GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds (M : ℕ) (hM : 0 < M) :
    {c : FiniteAdeleRing (𝓞 F) F | ∃ a : FiniteAdeleRing (𝓞 F) F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a} ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by sorry
