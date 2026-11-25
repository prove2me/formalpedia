-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_two_mul
-- name    : GroundTheory.Global.Elliptic.weierstrassLaurentCoeff_two_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:10:25.051802+00:00
-- url     : https://prove2.me/theorems/a8a6aa9b-ea95-4bbc-bd6d-07d100a37c1b
-- title:
--   Elliptic: weierstrass Laurent Coeff two mul
-- statement:
--   The Elliptic construction uses the weierstrass Laurent Coeff two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L238-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L238-L242

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

theorem GroundTheory.Global.Elliptic.weierstrassLaurentCoeff_two_mul {n : ℕ} (hn : n ≠ 0) :
    weierstrassLaurentCoeff L (2 * n) = (2 * n + 1) * L.G (2 * n + 2) := by sorry
