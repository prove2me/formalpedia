-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_map_toO
-- name    : GlobalTheory.CompanionTheory.QL.VolK.map_toO
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:27:26.326543+00:00
-- url     : https://prove2.me/theorems/082d652a-bcae-4011-b914-ef7e35e5aa3a
-- title:
--   Vol K: map to O
-- statement:
--   The Vol K construction uses the map to O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L74-L77

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

theorem GlobalTheory.CompanionTheory.QL.VolK.map_toO {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    (𝒪[F].subtype).mapMatrix (toO h) = x := by sorry
