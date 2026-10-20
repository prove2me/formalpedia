-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPresentWallSignedNodeSeparation_presentWall_ne_signedAmbientNode
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation.presentWall_ne_signedAmbientNode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:12.645026+00:00
-- url     : https://prove2.me/theorems/bcea6a48-b841-4601-a886-2f0e9e0034a1
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation.presentWall_ne_signedAmbientNode
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPresentWallSignedNodeSeparation.presentWall_ne_signedAmbientNode
    {r n : ℕ} {lam : Fin (r + 2) → ℕ}
    {mu : Fin (r + 1) → ℕ}
    (hfinite : FiniteInterlacing (n + 1) lam mu)
    (hlast : 0 < lam (Fin.last (r + 1)))
    (z : Fin (r + 2) × Bool) :
    -(wallShift (n + 1) (r + 1)) ≠
      signedNode (ambientShift (n + 1) lam) z := by sorry
