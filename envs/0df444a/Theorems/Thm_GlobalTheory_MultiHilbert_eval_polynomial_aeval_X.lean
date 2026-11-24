-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_eval_polynomial_aeval_X
-- name    : GlobalTheory.MultiHilbert.eval_polynomial_aeval_X
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:51.483207+00:00
-- url     : https://prove2.me/theorems/83900d77-8322-44aa-bf20-9a9fd10df4fd
-- title:
--   Multi Hilbert: eval polynomial aeval X
-- statement:
--   The Multi Hilbert construction uses the eval polynomial aeval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L62-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsMultigradedHilbertPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MultiHilbert
open MvPolynomial
variable {r : ℕ}

theorem GlobalTheory.MultiHilbert.eval_polynomial_aeval_X (x : Fin r → ℚ) (k : Fin r) (p : Polynomial ℚ) :
    eval x (Polynomial.aeval (X k : MvPolynomial (Fin r) ℚ) p) = p.eval (x k) := by sorry
