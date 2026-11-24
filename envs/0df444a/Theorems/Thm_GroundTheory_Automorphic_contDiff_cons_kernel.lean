-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_contDiff_cons_kernel
-- name    : GroundTheory.Automorphic.contDiff_cons_kernel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:56.803151+00:00
-- url     : https://prove2.me/theorems/c7604d0a-5579-4378-a869-a501091ed24b
-- title:
--   Automorphic: cont Diff cons kernel
-- statement:
--   The Automorphic construction uses the cont Diff cons kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L28-L31

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

theorem GroundTheory.Automorphic.contDiff_cons_kernel {d : ℕ} {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a)
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) := by sorry
