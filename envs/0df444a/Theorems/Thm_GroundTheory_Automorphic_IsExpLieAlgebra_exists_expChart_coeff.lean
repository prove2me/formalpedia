-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_expChart_coeff
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_expChart_coeff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:31:27.153462+00:00
-- url     : https://prove2.me/theorems/d2f054b9-b0d5-490d-bcc9-bba626e8ce7f
-- title:
--   Is Exp Lie Algebra: exists exp Chart coeff
-- statement:
--   The Is Exp Lie Algebra construction uses the exists exp Chart coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L137-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L137-L202

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_expChart_coeff {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ r > 0, ∃ c : 𝔤 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ X, AnalyticOnNhd ℝ (c X) (Metric.ball 0 r)) ∧
      (∀ X, c X 0 = (coordEquiv b).symm X) ∧
      ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ (g : G),
        ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) r,
          h.rightDeriv X f (g * h.expG (coordEquiv b x)) =
            fderiv ℝ (fun y => f (g * h.expG (coordEquiv b y))) x (c X x) := by sorry
