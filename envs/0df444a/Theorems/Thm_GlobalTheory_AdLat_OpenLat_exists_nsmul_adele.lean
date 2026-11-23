-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele
-- name    : GlobalTheory.AdLat.OpenLat.exists_nsmul_adele
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:15.533802+00:00
-- url     : https://prove2.me/theorems/2d4b6cc7-92fe-44c3-9ddf-a452b3b49643
-- title:
--   Open Lat: exists nsmul adele
-- statement:
--   The Open Lat construction uses the exists nsmul adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean#L25-L33

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

theorem GlobalTheory.AdLat.OpenLat.exists_nsmul_adele (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → N • a ∈ U := by sorry
