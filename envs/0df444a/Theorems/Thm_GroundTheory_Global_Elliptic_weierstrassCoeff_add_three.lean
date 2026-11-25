-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassCoeff_add_three
-- name    : GroundTheory.Global.Elliptic.weierstrassCoeff_add_three
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:09:09.582059+00:00
-- url     : https://prove2.me/theorems/6ff5991d-d761-5fe0-a27b-ba00620b9245
-- title:
--   Elliptic: weierstrass Coeff add three
-- statement:
--   The Elliptic construction uses the weierstrass Coeff add three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L37-L40

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
variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]

theorem GroundTheory.Global.Elliptic.weierstrassCoeff_add_three (a b : R) (n : ℕ) :
    weierstrassCoeff a b (n + 3) = (3 / ((2 * ((n : ℚ) + 3) + 3) * ((n : ℚ) + 1)) : ℚ) •
      ∑ i : Fin (n + 1), weierstrassCoeff a b (i + 1) * weierstrassCoeff a b (n + 1 - i) := by sorry
