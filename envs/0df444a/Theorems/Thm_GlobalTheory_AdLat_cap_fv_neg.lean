-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_cap_fv_neg
-- name    : GlobalTheory.AdLat.cap_fv_neg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:12.487806+00:00
-- url     : https://prove2.me/theorems/702dd2ab-45f8-4c52-bbe6-353b18c42c24
-- title:
--   Ad Lat: cap fv neg
-- statement:
--   The Ad Lat construction uses the cap fv neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionRationalPointsAndApproximation.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionRationalPointsAndApproximation.lean#L23-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
omit [NumberField E]

theorem GlobalTheory.AdLat.cap_fv_neg (x : Fin n → E) : fv F (-x) = - fv F x := by sorry
