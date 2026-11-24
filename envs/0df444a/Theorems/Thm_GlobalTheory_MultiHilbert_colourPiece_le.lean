-- Prove2me | Theorems.Thm_GlobalTheory_MultiHilbert_colourPiece_le
-- name    : GlobalTheory.MultiHilbert.colourPiece_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:29:49.390351+00:00
-- url     : https://prove2.me/theorems/bf33e8c8-dce7-456f-bbd6-a429b13a841e
-- title:
--   Multi Hilbert: colour Piece le
-- statement:
--   The Multi Hilbert construction uses the colour Piece le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L336-L357
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsMultigradedHilbertPoly.lean#L336-L357

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

theorem GlobalTheory.MultiHilbert.colourPiece_le {I : Ideal (MvPolynomial σ K)} (k : Fin r)
    (hk : ∀ i, col i = k → X i ∈ I) (n : Fin r → ℕ) (hn : 1 ≤ n k) :
    weightedHomogeneousSubmodule K (fun i => (Pi.single (col i) 1 : Fin r → ℕ)) n ≤
      I.restrictScalars K := by sorry
