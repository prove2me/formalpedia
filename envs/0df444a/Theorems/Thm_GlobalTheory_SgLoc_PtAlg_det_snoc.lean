-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_PtAlg_det_snoc
-- name    : GlobalTheory.SgLoc.PtAlg.det_snoc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:08.900677+00:00
-- url     : https://prove2.me/theorems/e841f2a2-b29d-4b4e-8513-2818126de632
-- title:
--   Pt Alg: det snoc
-- statement:
--   The Pt Alg construction uses the det snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SameBlockAppend.lean#L67-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SameBlockAppend.lean#L67-L77

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]

theorem GlobalTheory.SgLoc.PtAlg.det_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by sorry
