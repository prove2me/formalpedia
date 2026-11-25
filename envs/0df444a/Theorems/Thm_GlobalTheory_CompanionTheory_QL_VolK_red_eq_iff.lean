-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_red_eq_iff
-- name    : GlobalTheory.CompanionTheory.QL.VolK.red_eq_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:52.52526+00:00
-- url     : https://prove2.me/theorems/51e2b09e-5341-51de-b353-d26b540294ed
-- title:
--   Vol K: red eq iff
-- statement:
--   The Vol K construction uses the red eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L79-L84

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

theorem GlobalTheory.CompanionTheory.QL.VolK.red_eq_iff {ϖ : F} (hlt : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ 𝒪[F], x = ϖ * o)
    {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : red x = red y ↔ ∃ o ∈ 𝒪[F], x - y = ϖ * o := by sorry
