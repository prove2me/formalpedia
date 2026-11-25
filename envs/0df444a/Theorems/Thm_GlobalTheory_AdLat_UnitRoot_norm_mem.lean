-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_norm_mem
-- name    : GlobalTheory.AdLat.UnitRoot.norm_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:24.773555+00:00
-- url     : https://prove2.me/theorems/8cd541f6-402b-52a9-b5d7-54eafda71250
-- title:
--   Unit Root: norm mem
-- statement:
--   The Unit Root construction uses the norm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L138-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L138-L162

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

theorem GlobalTheory.AdLat.UnitRoot.norm_mem (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {z : RA F E}
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ b, z * sg (FiniteAdeleRing (𝓞 F) F) c z = incl F b ⊗ₜ[F] 1 := by sorry
