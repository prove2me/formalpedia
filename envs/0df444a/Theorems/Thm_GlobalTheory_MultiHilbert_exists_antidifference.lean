-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_exists_antidifference
-- name    : GlobalTheory.MultiHilbert.exists_antidifference
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:15.920561+00:00
-- url     : https://prove2.me/theorems/bb210b95-addf-4ee8-a4fb-3d69bce22d75
-- title:
--   Multi Hilbert: exists antidifference
-- statement:
--   The Multi Hilbert construction uses the exists antidifference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L78-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L78-L101

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

theorem GlobalTheory.MultiHilbert.exists_antidifference (Φ : MvPolynomial (Fin r) ℚ) (k : Fin r) :
    ∃ Ψ : MvPolynomial (Fin r) ℚ, ∀ x : Fin r → ℚ,
      eval (Function.update x k (x k + 1)) Ψ - eval x Ψ = eval x Φ := by sorry
