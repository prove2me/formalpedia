-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_eval
-- name    : GroundTheory.Global.Elliptic.analyticAt_eval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:50.665893+00:00
-- url     : https://prove2.me/theorems/278caa82-63f2-4cae-baa8-5b26ecc6ec09
-- title:
--   Elliptic: analytic At eval
-- statement:
--   The Elliptic construction uses the analytic At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L21-L23

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

theorem GroundTheory.Global.Elliptic.analyticAt_eval {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (P : ℂ[X]) :
    AnalyticAt ℂ (fun z ↦ P.eval (g z)) x := by sorry
