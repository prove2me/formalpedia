-- Prove2me | Theorems.Thm_GlobalTheory_SphereMeanDrop_measurePreserving_polar_gaussProb
-- name    : GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:39.466069+00:00
-- url     : https://prove2.me/theorems/36a9042f-59dc-4d63-8999-c29d81a8c905
-- title:
--   Sphere Mean Drop: measure Preserving polar gauss Prob
-- statement:
--   The Sphere Mean Drop construction uses the measure Preserving polar gauss Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPolarGaussianProbabilityComplex.lean#L13-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPolarGaussianProbabilityComplex.lean#L13-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPolarGaussianProbabilityComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanDrop

theorem GlobalTheory.SphereMeanDrop.measurePreserving_polar_gaussProb (n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun p : UnitSphereC n × Ioi (0:ℝ) => (p.2 : ℝ) • (p.1 : EuclideanSpace ℂ (Fin n)))
      ((sphereProb n).prod (radProb n)) (gaussProb n) := by sorry
