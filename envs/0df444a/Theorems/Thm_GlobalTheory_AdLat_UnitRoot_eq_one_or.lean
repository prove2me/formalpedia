-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_UnitRoot_eq_one_or
-- name    : GlobalTheory.AdLat.UnitRoot.eq_one_or
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:25:23.888104+00:00
-- url     : https://prove2.me/theorems/d95e80c1-84c4-4291-a8e1-ebd0acfc1a46
-- title:
--   Unit Root: eq one or
-- statement:
--   The Unit Root construction uses the eq one or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsIntegralUnitRootNormOneAdele.lean#L13-L23

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.AdLat.UnitRoot.eq_one_or (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (f : E ≃ₐ[F] E) : f = 1 ∨ f = c := by sorry
