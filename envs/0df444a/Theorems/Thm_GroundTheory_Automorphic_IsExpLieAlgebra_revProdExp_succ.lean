-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_succ
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.revProdExp_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:53.539162+00:00
-- url     : https://prove2.me/theorems/752d2b15-f79f-47bb-bd04-764c6baf3bf5
-- title:
--   Is Exp Lie Algebra: rev Prod Exp succ
-- statement:
--   The Is Exp Lie Algebra construction uses the rev Prod Exp succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L66-L68

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.revProdExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.revProdExp X t = h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) := by sorry
