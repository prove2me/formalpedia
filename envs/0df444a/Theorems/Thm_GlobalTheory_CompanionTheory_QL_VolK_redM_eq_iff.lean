-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_redM_eq_iff
-- name    : GlobalTheory.CompanionTheory.QL.VolK.redM_eq_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:25:18.179678+00:00
-- url     : https://prove2.me/theorems/d088ed76-be4f-5b30-8265-62beb79430e8
-- title:
--   Vol K: red M eq iff
-- statement:
--   The Vol K construction uses the red M eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L86-L96

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureUniformizerMultipleMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.VolK
variable {F : Type} [Field F] [ValuativeRel F]

theorem GlobalTheory.CompanionTheory.QL.VolK.redM_eq_iff {r : ℕ} {ϖ : F}
    (hlt : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ 𝒪[F], x = ϖ * o)
    {x y : Matrix (Fin r) (Fin r) F} (hx : x ∈ intMat 𝒪[F] r r) (hy : y ∈ intMat 𝒪[F] r r) :
    redM x = redM y ↔ x - y ∈ (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) := by sorry
