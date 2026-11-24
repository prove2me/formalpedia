-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_lt_meromorphicOrderAt_of_eventuallyEq
-- name    : GroundTheory.Global.Elliptic.lt_meromorphicOrderAt_of_eventuallyEq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:38:32.69622+00:00
-- url     : https://prove2.me/theorems/9a0d69b6-5e7e-4cef-ad54-4eacc9ffe5a4
-- title:
--   Elliptic: lt meromorphic Order At of eventually Eq
-- statement:
--   The Elliptic construction uses the lt meromorphic Order At of eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L49-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L49-L75

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

theorem GroundTheory.Global.Elliptic.lt_meromorphicOrderAt_of_eventuallyEq {f w : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hw : AnalyticAt ℂ w x) (hw0 : w x = 0)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n * w z) :
    (n : WithTop ℤ) < meromorphicOrderAt f x := by sorry
