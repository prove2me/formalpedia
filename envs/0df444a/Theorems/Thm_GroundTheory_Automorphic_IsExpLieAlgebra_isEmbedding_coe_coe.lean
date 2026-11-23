-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isEmbedding_coe_coe
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isEmbedding_coe_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:03.72052+00:00
-- url     : https://prove2.me/theorems/8e9e4aab-54a1-48ae-9123-86a4dd99bb7d
-- title:
--   Is Exp Lie Algebra: is Embedding coe coe
-- statement:
--   The Is Exp Lie Algebra construction uses the is Embedding coe coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L194-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L194-L196

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
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
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isEmbedding_coe_coe :
    Topology.IsEmbedding (fun x : G => ((x : 𝔸ˣ) : 𝔸)) := by sorry
