-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_sg_sg
-- name    : GlobalTheory.AdLat.UnitRoot.sg_sg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:50.487217+00:00
-- url     : https://prove2.me/theorems/40aecc4e-05c8-4ce8-a0cb-5d6b283b4152
-- title:
--   Unit Root: sg sg
-- statement:
--   The Unit Root construction uses the sg sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L111-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdele
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
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.UnitRoot
variable (F : Type) [Field F] [NumberField F]
variable (E : Type) [Field E] [NumberField E] [Algebra F E]
variable {F E}

theorem GlobalTheory.AdLat.UnitRoot.sg_sg (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (sg (FiniteAdeleRing (𝓞 F) F) c z) = z := by sorry
