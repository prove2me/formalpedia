-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_eq
-- name    : GroundTheory.Global.Elliptic.weierstrassLaurentCoeff_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:01.773639+00:00
-- url     : https://prove2.me/theorems/7696ad99-014d-5cc5-b0b7-9cc53e89ce72
-- title:
--   Elliptic: weierstrass Laurent Coeff eq
-- statement:
--   The Elliptic construction uses the weierstrass Laurent Coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L244-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L244-L283

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
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
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.weierstrassLaurentCoeff_eq (n : ℕ) (hn : n ≠ 0) :
    weierstrassLaurentCoeff L (2 * n) = weierstrassCoeff L.g₂ L.g₃ n := by sorry
