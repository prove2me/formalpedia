-- Prove2me | Theorems.Thm_GlobalTheory_SphereMeanDrop_blockSphereMean_incl
-- name    : GlobalTheory.SphereMeanDrop.blockSphereMean_incl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:32.884384+00:00
-- url     : https://prove2.me/theorems/48c61c6d-01c4-518d-b2a8-f104024d81eb
-- title:
--   Sphere Mean Drop: block Sphere Mean incl
-- statement:
--   The Sphere Mean Drop construction uses the block Sphere Mean incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMultiHomogeneousRenameCastLE.lean#L204-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMultiHomogeneousRenameCastLE.lean#L204-L243

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

theorem GlobalTheory.SphereMeanDrop.blockSphereMean_incl (B N n δ : ℕ) (f : MvPolynomial (Fin B × Fin N) ℂ) (hN : 0 < N)
    (hNn : N ≤ n) (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B n (GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f) =
      blockSphereMean B N f + (B : ℝ) * δ * ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by sorry
