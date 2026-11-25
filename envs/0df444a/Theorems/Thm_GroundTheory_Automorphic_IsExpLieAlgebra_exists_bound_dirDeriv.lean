-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_bound_dirDeriv
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_bound_dirDeriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:59.651779+00:00
-- url     : https://prove2.me/theorems/d4b679b9-c237-42a7-a085-840413949a3f
-- title:
--   Is Exp Lie Algebra: exists bound dir Deriv
-- statement:
--   The Is Exp Lie Algebra construction uses the exists bound dir Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L105-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L105-L198

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_bound_dirDeriv {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) :
    ∃ M : ℕ → ℝ, (∀ p x, ‖h.dirDeriv X p f x‖ ≤ M p) ∧
      ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) →
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞
          (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x)) ∧
        HasCompactSupport (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) := by sorry
