-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_integral_fin_succ_cons
-- name    : GroundTheory.Automorphic.integral_fin_succ_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:38:46.999727+00:00
-- url     : https://prove2.me/theorems/69cf6288-6bef-4e64-b18d-57949a86a1a5
-- title:
--   Automorphic: integral fin succ cons
-- statement:
--   The Automorphic construction uses the integral fin succ cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L12-L26

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

theorem GroundTheory.Automorphic.integral_fin_succ_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {F : (Fin (d + 1) → ℝ) → E} (hF : Integrable F) :
    ∫ t, F t = ∫ s, ∫ t', F (Fin.cons s t') := by sorry
