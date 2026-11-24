-- Prove2me | Theorems.Thm_GlobalTheory_RelDimFibCrit_exists_minimal_in_fibre
-- name    : GlobalTheory.RelDimFibCrit.exists_minimal_in_fibre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:38.740383+00:00
-- url     : https://prove2.me/theorems/29ad0343-35f7-4ea1-97f0-a959c3998f1f
-- title:
--   Rel Dim Fib Crit: exists minimal in fibre
-- statement:
--   The Rel Dim Fib Crit construction uses the exists minimal in fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L52-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L52-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit

theorem GlobalTheory.RelDimFibCrit.exists_minimal_in_fibre {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (P : Ideal B) (hP : P.IsPrime) :
    ∃ P₀ : Ideal B, P₀.IsPrime ∧ P₀ ≤ P ∧ P₀.comap φ = P.comap φ ∧
      ∀ P' : Ideal B, P'.IsPrime → P' ≤ P₀ → P'.comap φ = P.comap φ → P' = P₀ := by sorry
