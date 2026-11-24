-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_tmul_fixed
-- name    : GlobalTheory.AdLat.UnitRoot.tmul_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:31.6129+00:00
-- url     : https://prove2.me/theorems/551324c6-1bce-4c5a-b949-fdd75fe07787
-- title:
--   Unit Root: tmul fixed
-- statement:
--   The Unit Root construction uses the tmul fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L97-L106

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

theorem GlobalTheory.AdLat.UnitRoot.tmul_fixed (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    {a : FiniteAdeleRing (𝓞 F) F} (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {x : E}
    (hx : x ∈ Set.range (algebraMap (𝓞 E) E)) (hfix : c x = x) :
    ∃ b, (a ⊗ₜ[F] x : RA F E) = incl F b ⊗ₜ[F] 1 := by sorry
