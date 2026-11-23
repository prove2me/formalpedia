-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_eventually_nhdsNE_zero_eval_weierstrassP_ne_zero
-- name    : GroundTheory.Global.Elliptic.eventually_nhdsNE_zero_eval_weierstrassP_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:02.317718+00:00
-- url     : https://prove2.me/theorems/8ca21f38-4612-447e-94a2-b5af5a58708d
-- title:
--   Elliptic: eventually nhds NE zero eval weierstrass P ne zero
-- statement:
--   The Elliptic construction uses the eventually nhds NE zero eval weierstrass P ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L232-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L232-L241

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.eventually_nhdsNE_zero_eval_weierstrassP_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q.eval (℘[L] z) ≠ 0 := by sorry
