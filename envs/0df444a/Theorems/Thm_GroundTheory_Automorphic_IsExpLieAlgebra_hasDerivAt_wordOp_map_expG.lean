-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_wordOp_map_expG
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_wordOp_map_expG
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:40:18.424616+00:00
-- url     : https://prove2.me/theorems/5adb4794-b12b-4639-9731-3f011ac016c0
-- title:
--   Is Exp Lie Algebra: has Deriv At word Op map exp G
-- statement:
--   The Is Exp Lie Algebra construction uses the has Deriv At word Op map exp G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L306-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L306-L318

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_wordOp_map_expG (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    (X : 𝔤) (g : G) {k : ℕ} (Y : Fin k → 𝔤) :
    HasDerivAt (fun t : ℝ => h.wordOp π Y (π g (π (h.expG (t • X)) v)))
      (h.wordOp π Y (π g (h.derivOp π X v))) 0 := by sorry
