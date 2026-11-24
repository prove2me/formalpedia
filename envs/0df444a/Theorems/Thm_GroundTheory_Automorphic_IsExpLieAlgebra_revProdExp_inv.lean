-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_inv
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.revProdExp_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:59.876072+00:00
-- url     : https://prove2.me/theorems/1184f4f6-f023-4cba-833c-4957713b8ef9
-- title:
--   Is Exp Lie Algebra: rev Prod Exp inv
-- statement:
--   The Is Exp Lie Algebra construction uses the rev Prod Exp inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L83-L88

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
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
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.revProdExp_inv {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (h.revProdExp X t)⁻¹ = h.prodExp X (-t) := by sorry
