-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_sg_tmul
-- name    : GlobalTheory.AdLat.UnitRoot.sg_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:27.980826+00:00
-- url     : https://prove2.me/theorems/d7fb59c4-66db-4bf8-b0d4-2a534a614e0c
-- title:
--   Unit Root: sg tmul
-- statement:
--   The Unit Root construction uses the sg tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L108-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L108-L109

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

theorem GlobalTheory.AdLat.UnitRoot.sg_tmul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (x : E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a ⊗ₜ[F] x) = a ⊗ₜ[F] c x := by sorry
