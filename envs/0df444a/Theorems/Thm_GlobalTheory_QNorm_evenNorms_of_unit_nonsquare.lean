-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_evenNorms_of_unit_nonsquare
-- name    : GlobalTheory.QNorm.evenNorms_of_unit_nonsquare
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:40.894902+00:00
-- url     : https://prove2.me/theorems/b6f71fa8-9e4e-468e-938c-6949c80c2029
-- title:
--   QNorm: even Norms of unit nonsquare
-- statement:
--   The QNorm construction uses the even Norms of unit nonsquare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EvenNormsOfUnitNonsquare.lean#L9-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EvenNormsOfUnitNonsquare.lean#L9-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenNormsOfUnitNonsquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.evenNorms_of_unit_nonsquare {K : Type} [Field K] (w : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, w (x - 1) < 1 → IsSquare x) (δ : K) (hδ : w δ = 1) (hn : ¬ IsSquare δ) :
    EvenNorms w δ := by sorry
