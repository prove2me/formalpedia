-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_laurent
-- name    : GroundTheory.Global.Elliptic.analyticAt_weierstrassP_laurent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:02.33881+00:00
-- url     : https://prove2.me/theorems/c0881f8e-1988-4075-bbef-df6db4409ff0
-- title:
--   Elliptic: analytic At weierstrass P laurent
-- statement:
--   The Elliptic construction uses the analytic At weierstrass P laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L44-L47

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

theorem GroundTheory.Global.Elliptic.analyticAt_weierstrassP_laurent :
    AnalyticAt ℂ (fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1) 0 := by sorry
