-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_eval_monomial_erase
-- name    : GlobalTheory.MultiHilbert.eval_monomial_erase
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:42.398032+00:00
-- url     : https://prove2.me/theorems/4a859027-1cb5-4457-8b47-3414e85eacfd
-- title:
--   Multi Hilbert: eval monomial erase
-- statement:
--   The Multi Hilbert construction uses the eval monomial erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L68-L76

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

theorem GlobalTheory.MultiHilbert.eval_monomial_erase (x : Fin r → ℚ) (k : Fin r) (t : ℚ) (d : Fin r →₀ ℕ) (c : ℚ) :
    eval (Function.update x k t) (monomial (d.erase k) c) = eval x (monomial (d.erase k) c) := by sorry
