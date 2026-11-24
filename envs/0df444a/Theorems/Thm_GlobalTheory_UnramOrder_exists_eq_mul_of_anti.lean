-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_mul_of_anti
-- name    : GlobalTheory.UnramOrder.exists_eq_mul_of_anti
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:39.471477+00:00
-- url     : https://prove2.me/theorems/fdc3f2c1-2e59-4681-95c2-864dbb202e7e
-- title:
--   Unram Order: exists eq mul of anti
-- statement:
--   The Unram Order construction uses the exists eq mul of anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L247-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L247-L259

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.UnramOrder.exists_eq_mul_of_anti (L : LocE F E) {y z : E} (hy : L.cj y = -y) (hz : L.cj z = -z)
    (hz0 : z ≠ 0) : ∃ c : F, y = algebraMap F E c * z := by sorry
