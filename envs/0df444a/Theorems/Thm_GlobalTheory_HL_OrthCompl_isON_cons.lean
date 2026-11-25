-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_isON_cons
-- name    : GlobalTheory.HL.OrthCompl.isON_cons
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:01.274677+00:00
-- url     : https://prove2.me/theorems/40a1f85c-4c8a-5ff4-8d8d-6793c33ae9c2
-- title:
--   Orth Compl: is ON cons
-- statement:
--   The Orth Compl construction uses the is ON cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L172-L180

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.HL.OrthCompl.isON_cons (h : IsHerm L Hm) {k : ℕ} {v : Fin n → E} {e : Fin k → Fin n → E}
    (hv : hf L Hm v v = 1) (hev : ∀ i, hf L Hm (e i) v = 0) (he : IsON L Hm e) :
    IsON L Hm (Fin.cons v e : Fin (k + 1) → Fin n → E) := by sorry
