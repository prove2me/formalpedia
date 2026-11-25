-- Prove2me | Theorems.Thm_GlobalTheory_HL_SameTrace_shear_mem_isomG
-- name    : GlobalTheory.HL.SameTrace.shear_mem_isomG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:34:18.268471+00:00
-- url     : https://prove2.me/theorems/b75b5160-07a4-46a3-8c7e-dca3f2266a3f
-- title:
--   Same Trace: shear mem isom G
-- statement:
--   The Same Trace construction uses the shear mem isom G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfSameTrace.lean#L72-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsIsometryOfSameTrace.lean#L72-L94

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DualInterSelfDualHermitianLatticeSubspaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryOfSameTrace
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SameTrace
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HL.SameTrace.shear_mem_isomG {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {m : ℕ}
    (b c d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (hdd : ∀ i j, hf L Hm (d i) (d j) = 0)
    (hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k))
    (hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0) :
    shear L Hm b d hdb ∈ isomG L Hm := by sorry
