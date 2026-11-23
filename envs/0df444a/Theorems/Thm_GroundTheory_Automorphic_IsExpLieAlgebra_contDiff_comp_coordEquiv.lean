-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_coordEquiv
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_coordEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:35.553023+00:00
-- url     : https://prove2.me/theorems/81df98ce-b1f5-4346-afb0-43ff3b48ba90
-- title:
--   Is Exp Lie Algebra: cont Diff comp coord Equiv
-- statement:
--   The Is Exp Lie Algebra construction uses the cont Diff comp coord Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ContDiffCompCoordEquiv.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ContDiffCompCoordEquiv.lean#L28-L31

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_coordEquiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : G → F} (hf : h.IsSmoothFun f) (g : G) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin d) => f (g * h.expG (coordEquiv b x))) := by sorry
