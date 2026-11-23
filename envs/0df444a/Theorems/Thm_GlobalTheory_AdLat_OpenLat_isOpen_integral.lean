-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_OpenLat_isOpen_integral
-- name    : GlobalTheory.AdLat.OpenLat.isOpen_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:45.250017+00:00
-- url     : https://prove2.me/theorems/70834da0-d1c9-47bc-9b71-da1ac012c0db
-- title:
--   Open Lat: is Open integral
-- statement:
--   The Open Lat construction uses the is Open integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenNsmulAdelicCompletionOfVectorSet.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_NsmulIntegralMemNhdsZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Theorems.Thm_GlobalTheory_IntegralNeighbourhoodZero_isOpen_integral
import Theorems.Thm_GlobalTheory_IntegralOpen_isOpen_integral

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

theorem GlobalTheory.AdLat.OpenLat.isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} := by sorry
