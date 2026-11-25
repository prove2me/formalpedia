-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_card_scaled
-- name    : GlobalTheory.CompanionTheory.QL.VolK.card_scaled
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:33.667668+00:00
-- url     : https://prove2.me/theorems/b027a079-1811-4219-b71a-cda340f60e18
-- title:
--   Vol K: card scaled
-- statement:
--   The Vol K construction uses the card scaled property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L11-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L11-L52

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

theorem GlobalTheory.CompanionTheory.QL.VolK.card_scaled (q r : ℕ) (hq : 0 < q) :
    (((∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) : ℕ)) : ℝ) * (q : ℝ) ^ (-((r * r : ℕ) : ℤ)) = qE q 1 r := by sorry
