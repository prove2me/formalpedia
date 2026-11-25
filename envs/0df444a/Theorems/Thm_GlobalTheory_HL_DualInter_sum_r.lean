-- Prove2me | Theorems.Thm_GlobalTheory_HL_DualInter_sum_r
-- name    : GlobalTheory.HL.DualInter.sum_r
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:07:40.23081+00:00
-- url     : https://prove2.me/theorems/e35c62dd-227e-57eb-9e47-3a386f481094
-- title:
--   Dual Inter: sum r
-- statement:
--   The Dual Inter construction uses the sum r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DualInterSelfDualHermitianLatticeSubspace.lean#L38-L40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspace
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.DualInter
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HL.DualInter.sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (x : Fin n → E) :
    hf L Hm x (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm x (a i) := by sorry
