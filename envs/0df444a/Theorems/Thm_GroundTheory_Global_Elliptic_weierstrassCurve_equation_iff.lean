-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCurve_equation_iff
-- name    : GroundTheory.Global.Elliptic.weierstrassCurve_equation_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:05:45.532596+00:00
-- url     : https://prove2.me/theorems/564ef946-564f-51e0-9fbc-5a4616039686
-- title:
--   Elliptic: weierstrass Curve equation iff
-- statement:
--   The Elliptic construction uses the weierstrass Curve equation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Uniformization.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Uniformization.lean#L38-L48

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)

theorem GroundTheory.Global.Elliptic.weierstrassCurve_equation_iff (x Y : ℂ) :
    (weierstrassCurve L).toAffine.Equation x Y ↔
      (2 * Y) ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by sorry
