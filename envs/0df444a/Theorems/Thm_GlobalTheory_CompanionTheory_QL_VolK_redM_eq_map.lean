-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_VolK_redM_eq_map
-- name    : GlobalTheory.CompanionTheory.QL.VolK.redM_eq_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:41.378781+00:00
-- url     : https://prove2.me/theorems/e4061576-7485-43d4-bcd7-e2dd3dc8dec8
-- title:
--   Vol K: red M eq map
-- statement:
--   The Vol K construction uses the red M eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MeasureInvertibleIntegralMatrices.lean#L69-L72

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

theorem GlobalTheory.CompanionTheory.QL.VolK.redM_eq_map {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    redM x = (IsLocalRing.residue 𝒪[F]).mapMatrix (toO h) := by sorry
