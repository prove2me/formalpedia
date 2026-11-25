-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_isON_orth_family
-- name    : GlobalTheory.HL.OrthCompl.exists_isON_orth_family
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:33:07.668106+00:00
-- url     : https://prove2.me/theorems/76593308-9f51-4c88-8af7-3e76f6150d9a
-- title:
--   Orth Compl: exists is ON orth family
-- statement:
--   The Orth Compl construction uses the exists is ON orth family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L301-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L301-L311

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
variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem GlobalTheory.HL.OrthCompl.exists_isON_orth_family (h : IsHerm L Hm) (k m : ℕ) :
    ∀ (y : Fin m → Fin n → E) (M : Submodule L.O (Fin n → E)) (e : Fin (k + 2 * m) → Fin n → E),
      (∀ i, e i ∈ M) → IsON L Hm e →
      ∃ u : Fin k → Fin n → E, (∀ i, u i ∈ M ∧ ∀ j, hf L Hm (u i) (y j) = 0) ∧ IsON L Hm u := by sorry
