-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_prodExpVal_succ
-- name    : GroundTheory.Automorphic.prodExpVal_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:19.457323+00:00
-- url     : https://prove2.me/theorems/5a9cb4b6-16a3-4d81-85c6-de8f9fe619f7
-- title:
--   Automorphic: prod Exp Val succ
-- statement:
--   The Automorphic construction uses the prod Exp Val succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L16-L18

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

theorem GroundTheory.Automorphic.prodExpVal_succ {d : ℕ} (X : Fin (d + 1) → 𝔸) (t : Fin (d + 1) → ℝ) :
    prodExpVal X t = exp (t 0 • X 0) * prodExpVal (fun i => X i.succ) (fun i => t i.succ) := by sorry
