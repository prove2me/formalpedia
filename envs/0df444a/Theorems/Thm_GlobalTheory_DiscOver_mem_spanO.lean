-- Prove2me | Theorems.Thm_GlobalTheory_DiscOver_mem_spanO
-- name    : GlobalTheory.DiscOver.mem_spanO
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:39:56.229464+00:00
-- url     : https://prove2.me/theorems/2ddb3ac4-8891-409e-aa13-290e2c30277d
-- title:
--   Disc Over: mem span O
-- statement:
--   The Disc Over construction uses the mem span O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L104-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardDiscriminantModuleIntegralOverlatticeSpan.lean#L104-L111

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

theorem GlobalTheory.DiscOver.mem_spanO (L : LocE F E) {n m : ℕ} (w : Fin m → Fin n → E) (x : Fin n → E) :
    x ∈ Submodule.span L.O (Set.range w) ↔ ∃ s : Fin m → E, (∀ i, s i ∈ L.O) ∧ ∑ i, s i • w i = x := by sorry
