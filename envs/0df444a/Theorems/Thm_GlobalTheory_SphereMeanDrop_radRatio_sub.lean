-- Prove2me | Theorems.Thm_GlobalTheory_SphereMeanDrop_radRatio_sub
-- name    : GlobalTheory.SphereMeanDrop.radRatio_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:22:24.973999+00:00
-- url     : https://prove2.me/theorems/c53e232b-732e-4ea2-a265-ddecaf0a97b4
-- title:
--   Sphere Mean Drop: rad Ratio sub
-- statement:
--   The Sphere Mean Drop construction uses the rad Ratio sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMultiHomogeneousRenameCastLE.lean#L193-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMultiHomogeneousRenameCastLE.lean#L193-L202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianRadialLawProbabilityLogIntegrableMeanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreservingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsMultiHomogeneousRenameCastLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights

theorem GlobalTheory.SphereMeanDrop.radRatio_sub {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    radK (2 * N - 1) / radJ (2 * N - 1) - radK (2 * n - 1) / radJ (2 * n - 1) =
      ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by sorry
