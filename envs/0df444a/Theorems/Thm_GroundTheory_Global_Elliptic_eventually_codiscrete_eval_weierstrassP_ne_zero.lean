-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_eval_weierstrassP_ne_zero
-- name    : GroundTheory.Global.Elliptic.eventually_codiscrete_eval_weierstrassP_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:05.863792+00:00
-- url     : https://prove2.me/theorems/000d629a-406a-4e41-bd99-89a79f27dcef
-- title:
--   Elliptic: eventually codiscrete eval weierstrass P ne zero
-- statement:
--   The Elliptic construction uses the eventually codiscrete eval weierstrass P ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L253-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L253-L256

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

theorem GroundTheory.Global.Elliptic.eventually_codiscrete_eval_weierstrassP_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in codiscrete ℂ, Q.eval (℘[L] z) ≠ 0 := by sorry
