-- Prove2me | Theorems.Thm_GlobalTheory_SphereMeanDrop_linSubst_incl
-- name    : GlobalTheory.SphereMeanDrop.linSubst_incl
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:59.075956+00:00
-- url     : https://prove2.me/theorems/e9555e88-f6fc-4a01-be23-12082c60d32a
-- title:
--   Sphere Mean Drop: lin Subst incl
-- statement:
--   The Sphere Mean Drop construction uses the lin Subst incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMultiHomogeneousRenameCastLE.lean#L46-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsMultiHomogeneousRenameCastLE.lean#L46-L64

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

theorem GlobalTheory.SphereMeanDrop.linSubst_incl {B N n : ℕ} (h : N ≤ n) (f : MvPolynomial (Fin B × Fin N) ℂ) :
    GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
                 if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f =
      rename (fun p : Fin B × Fin N => (p.1, Fin.castLE h p.2)) f := by sorry
