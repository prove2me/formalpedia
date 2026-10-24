-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_eventually_nonzero_actualMinor
-- name    : OAI.PiExponent.DeterminantContradiction.eventually_nonzero_actualMinor
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-23T06:56:24.319797+00:00
-- url     : https://prove2.me/theorems/e2fd1c3b-b495-4621-92de-390c16b3db4f
-- title:
--   Eventual nonvanishing of a full-row interpolation minor
-- statement:
--   For all sufficiently large heights, the exact truncated-log interpolation matrix has an injective selection of columns whose square minor on all strict-cutoff rows is nonsingular. This preserves both the strict row cutoff and the fixed truncation orders. It removes the quantitative rank-existence work from the parent. A proof route is to establish the weighted curve-contact bound for the logarithmic center ideals, pass to ordinary ideal-power representatives with subcritical weighted degree, and use those representatives to obtain row independence; the cited specialized jet-surjectivity route is another source-backed route to investigate. The essential unresolved work is the quantitative interpolation/rank estimate.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.eventually_nonzero_actualMinor
    (nu : Real) (d : FixedData nu) :
    ∀ᶠ H : Real in atTop,
      ∃ selection : Row d H → Column d H,
        Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0 := by sorry
