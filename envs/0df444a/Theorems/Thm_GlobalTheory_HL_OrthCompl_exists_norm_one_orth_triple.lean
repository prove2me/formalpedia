-- Prove2me | Theorems.Thm_GlobalTheory_HL_OrthCompl_exists_norm_one_orth_triple
-- name    : GlobalTheory.HL.OrthCompl.exists_norm_one_orth_triple
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:35:53.20624+00:00
-- url     : https://prove2.me/theorems/08b8c5d7-23da-52b3-96a6-4f547f2fc566
-- title:
--   Orth Compl: exists norm one orth triple
-- statement:
--   The Orth Compl construction uses the exists norm one orth triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L184-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsNormOneOrthTriple.lean#L184-L219

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

theorem GlobalTheory.HL.OrthCompl.exists_norm_one_orth_triple (y0 y1 y2 : E) :
    ∃ u0 ∈ L.O, ∃ u1 ∈ L.O, ∃ u2 ∈ L.O, u0 * L.cj u0 + u1 * L.cj u1 + u2 * L.cj u2 = 1 ∧
      u0 * y0 + u1 * y1 + u2 * y2 = 0 := by sorry
