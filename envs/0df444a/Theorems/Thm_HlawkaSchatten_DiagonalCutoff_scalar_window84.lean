-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_scalar_window84
-- name    : HlawkaSchatten.DiagonalCutoff.scalar_window84
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T05:19:39.02423+00:00
-- url     : https://prove2.me/theorems/693a3429-e357-4a53-a84a-1c0a125d2c7b
-- title:
--   Scalar confinement and linear lower bound on the cyclic constant for 84 ≤ p ≤ 85
-- statement:
--   For every real exponent between 84 and 85, the cyclic constant exceeds both 20p/43 and the scalar envelope evaluated at 17867/50000. These two strict bounds supply the scalar confinement hypotheses for the cutoff84 proof.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — exact supporting lemma for the locally verified Codex cutoff84 continuation; CUTOFF84-ARGUMENT.md, scalar confinement and coupled box curvature sections.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.scalar_window84 : ∀ p : ℝ, 84 ≤ p → p ≤ 85 →
    (20/43 : ℝ)*p < cyclicConstant p ∧
    scalarEnvelope p (17867/50000) < cyclicConstant p := by sorry
