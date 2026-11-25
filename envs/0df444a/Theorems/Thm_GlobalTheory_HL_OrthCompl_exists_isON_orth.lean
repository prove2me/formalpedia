-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_isON_orth
-- name    : GlobalTheory.HL.OrthCompl.exists_isON_orth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:07.795203+00:00
-- url     : https://prove2.me/theorems/5e8c2fa6-1897-57a8-8e99-db51e6d70e5c
-- title:
--   Orth Compl: exists is ON orth
-- statement:
--   The Orth Compl construction uses the exists is ON orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L267-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L267-L299

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

theorem GlobalTheory.HL.OrthCompl.exists_isON_orth (h : IsHerm L Hm) (y : Fin n → E) (k : ℕ) :
    ∀ (M : Submodule L.O (Fin n → E)) (e : Fin (k + 2) → Fin n → E), (∀ i, e i ∈ M) →
      IsON L Hm e → ∃ u : Fin k → Fin n → E, (∀ i, u i ∈ M ⊓ orthTo L Hm y) ∧ IsON L Hm u := by sorry
