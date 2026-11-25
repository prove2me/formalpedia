-- Prove2me | Theorems.Thm_GlobalTheory_DiscOver_sum_comb
-- name    : GlobalTheory.DiscOver.sum_comb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:59:10.36988+00:00
-- url     : https://prove2.me/theorems/382e32bf-da03-45c1-99ba-97fe1934176e
-- title:
--   Disc Over: sum comb
-- statement:
--   The Disc Over construction uses the sum comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L79-L83

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexSpanLatticeMatrixDetNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardDiscriminantModuleIntegralOverlatticeSpan
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
open GlobalTheory GlobalTheory.DiscOver
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.DiscOver.sum_comb {n m : ℕ} (w : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) (s : Fin m → E) :
    ∑ j, s j • comb w A j = ∑ i, (A.mulVec s) i • w i := by sorry
