-- Prove2me | Theorems.Thm_GlobalTheory_HL_SelfDual_sum_hf_smul
-- name    : GlobalTheory.HL.SelfDual.sum_hf_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:33:43.993097+00:00
-- url     : https://prove2.me/theorems/b2c2147e-7ee3-4c13-8cb7-49c851b432d1
-- title:
--   Self Dual: sum hf smul
-- statement:
--   The Self Dual construction uses the sum hf smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrthonormalBasisAndOneOrbit.lean#L151-L157

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.SelfDual
open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.SelfDual.sum_hf_smul (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) (x : Fin n → E) :
    ∑ i, hf L Hm x (b i) • b i = x := by sorry
