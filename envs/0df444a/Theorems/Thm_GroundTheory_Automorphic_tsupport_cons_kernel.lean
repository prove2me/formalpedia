-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tsupport_cons_kernel
-- name    : GroundTheory.Automorphic.tsupport_cons_kernel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:40.898168+00:00
-- url     : https://prove2.me/theorems/b2e30b21-95f6-4384-aa59-676e8b0fd293
-- title:
--   Automorphic: tsupport cons kernel
-- statement:
--   The Automorphic construction uses the tsupport cons kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L33-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinProducts.lean#L33-L51

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

theorem GroundTheory.Automorphic.tsupport_cons_kernel {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ}
    (has : tsupport a ⊆ Icc (-ε) ε)
    (hKs : tsupport K ⊆ Metric.closedBall 0 ε) :
    tsupport (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) ⊆ Metric.closedBall 0 ε := by sorry
