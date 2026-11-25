-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_iteratedDeriv_weierstrassPExcept_zero
-- name    : GroundTheory.Global.Elliptic.iteratedDeriv_weierstrassPExcept_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:50:32.343609+00:00
-- url     : https://prove2.me/theorems/14c3c371-f6c7-5e66-9aee-99079b5781bc
-- title:
--   Elliptic: iterated Deriv weierstrass PExcept zero
-- statement:
--   The Elliptic construction uses the iterated Deriv weierstrass PExcept zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L99-L106

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

theorem GroundTheory.Global.Elliptic.iteratedDeriv_weierstrassPExcept_zero (j : ℕ) :
    iteratedDeriv j ℘[L - (0 : ℂ)] 0 = j ! * weierstrassLaurentCoeff L j := by sorry
