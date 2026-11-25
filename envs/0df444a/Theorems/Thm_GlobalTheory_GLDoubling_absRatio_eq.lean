-- Prove2me | Theorems.Thm_GlobalTheory_GLDoubling_absRatio_eq
-- name    : GlobalTheory.GLDoubling.absRatio_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:55.136171+00:00
-- url     : https://prove2.me/theorems/1be80382-7bfc-4375-9c1b-e0c5268d57d0
-- title:
--   GLDoubling: abs Ratio eq
-- statement:
--   The GLDoubling construction uses the abs Ratio eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L37-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}

theorem GlobalTheory.GLDoubling.absRatio_eq (p : siegel k n) {a d : kˣ} (ha : (a : k) = (leviMat (Equiv.refl (n ⊕ n)) p.1.1).det)
    (hd : (d : k) = (quotMat (Equiv.refl (n ⊕ n)) p.1.1).det) : (absRatio k n p : ℝ) = nabs k a / nabs k d := by sorry
