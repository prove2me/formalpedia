-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_contDiff_comp_expG_smul_mul_mul_expG
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_expG_smul_mul_mul_expG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:43.753827+00:00
-- url     : https://prove2.me/theorems/fec1e041-e8ad-4ef0-ac50-673f49c4f97e
-- title:
--   Is Exp Lie Algebra: cont Diff comp exp G smul mul mul exp G
-- statement:
--   The Is Exp Lie Algebra construction uses the cont Diff comp exp G smul mul mul exp G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L67-L76

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.contDiff_comp_expG_smul_mul_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (g : G) :
    ContDiff ℝ ∞ (fun q : 𝔤 × ℝ => f (h.expG (q.2 • X) * (g * h.expG q.1))) := by sorry
