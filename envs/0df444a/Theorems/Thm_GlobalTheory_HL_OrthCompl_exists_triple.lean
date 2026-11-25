-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_triple
-- name    : GlobalTheory.HL.OrthCompl.exists_triple
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:35:54.34851+00:00
-- url     : https://prove2.me/theorems/3b62ae39-1240-5f3c-9a6e-51d742becf15
-- title:
--   Orth Compl: exists triple
-- statement:
--   The Orth Compl construction uses the exists triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L221-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L221-L265

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

theorem GlobalTheory.HL.OrthCompl.exists_triple (h : IsHerm L Hm) (M : Submodule L.O (Fin n → E)) {e0 e1 e2 : Fin n → E}
    (m0 : e0 ∈ M) (m1 : e1 ∈ M) (m2 : e2 ∈ M)
    (h00 : hf L Hm e0 e0 = 1) (h11 : hf L Hm e1 e1 = 1) (h22 : hf L Hm e2 e2 = 1)
    (h01 : hf L Hm e0 e1 = 0) (h02 : hf L Hm e0 e2 = 0) (h12 : hf L Hm e1 e2 = 0)
    (y : Fin n → E) :
    ∃ u ∈ M, ∃ t ∈ M, ∃ s ∈ M, hf L Hm u u = 1 ∧ hf L Hm t t = 1 ∧ hf L Hm s s = 1 ∧
      hf L Hm t u = 0 ∧ hf L Hm s u = 0 ∧ hf L Hm s t = 0 ∧ hf L Hm u y = 0 := by sorry
