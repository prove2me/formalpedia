-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_val_prodExp
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.val_prodExp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:12.477108+00:00
-- url     : https://prove2.me/theorems/c4acca17-4ab1-4911-9aa5-2a8f4314bfee
-- title:
--   Is Exp Lie Algebra: val prod Exp
-- statement:
--   The Is Exp Lie Algebra construction uses the val prod Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L203-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L203-L208

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.val_prodExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (((h.prodExp X t : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (X i : 𝔸)) t := by sorry
