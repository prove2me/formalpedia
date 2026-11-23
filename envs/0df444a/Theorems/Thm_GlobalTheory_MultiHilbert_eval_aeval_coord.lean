-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_eval_aeval_coord
-- name    : GlobalTheory.MultiHilbert.eval_aeval_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:48.449804+00:00
-- url     : https://prove2.me/theorems/4b230848-15fb-4a64-a93d-80dc4b7a149a
-- title:
--   Multi Hilbert: eval aeval coord
-- statement:
--   The Multi Hilbert construction uses the eval aeval coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L25-L31

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

theorem GlobalTheory.MultiHilbert.eval_aeval_coord (x : Fin r → ℚ) (p : Fin r → MvPolynomial (Fin r) ℚ)
    (Φ : MvPolynomial (Fin r) ℚ) :
    eval x (aeval p Φ) = eval (fun k => eval x (p k)) Φ := by sorry
