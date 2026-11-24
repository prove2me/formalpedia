-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_finite_colourPiece
-- name    : GlobalTheory.MultiHilbert.finite_colourPiece
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:25.513614+00:00
-- url     : https://prove2.me/theorems/b6bab038-bbef-468a-b253-3a86ef2a27a2
-- title:
--   Multi Hilbert: finite colour Piece
-- statement:
--   The Multi Hilbert construction uses the finite colour Piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L309-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L309-L334

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
variable {K σ : Type} [Field K] {r : ℕ} (col : σ → Fin r)

theorem GlobalTheory.MultiHilbert.finite_colourPiece [Finite σ] (n : Fin r → ℕ) :
    Module.Finite K (weightedHomogeneousSubmodule K
      (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n) := by sorry
