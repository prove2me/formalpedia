-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_dirDeriv_eq_zero_of_notMem
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.dirDeriv_eq_zero_of_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:56.379301+00:00
-- url     : https://prove2.me/theorems/393882d5-dc6d-48d6-b085-f397413aaffb
-- title:
--   Is Exp Lie Algebra: dir Deriv eq zero of not Mem
-- statement:
--   The Is Exp Lie Algebra construction uses the dir Deriv eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L78-L90

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.dirDeriv_eq_zero_of_notMem {f : G → ℂ} (X : 𝔤) (p : ℕ) {x : G}
    (hx : x ∉ tsupport f) : h.dirDeriv X p f x = 0 := by sorry
