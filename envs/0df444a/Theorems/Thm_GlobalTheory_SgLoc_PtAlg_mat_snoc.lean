-- Prove2me | Theorems.Thm_GlobalTheory_SgLoc_PtAlg_mat_snoc
-- name    : GlobalTheory.SgLoc.PtAlg.mat_snoc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:17.578418+00:00
-- url     : https://prove2.me/theorems/5086f53a-75f1-48c6-a2a3-2e3aef4003b3
-- title:
--   Pt Alg: mat snoc
-- statement:
--   The Pt Alg construction uses the mat snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SameBlockAppend.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SameBlockAppend.lean#L31-L37

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

theorem GlobalTheory.SgLoc.PtAlg.mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by sorry
