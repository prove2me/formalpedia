-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_hasSum_weierstrassP_laurent
-- name    : GroundTheory.Global.Elliptic.hasSum_weierstrassP_laurent
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:53:01.76458+00:00
-- url     : https://prove2.me/theorems/0f3ce7f0-9637-5890-b75f-28941f8f88ef
-- title:
--   Elliptic: has Sum weierstrass P laurent
-- statement:
--   The Elliptic construction uses the has Sum weierstrass P laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L227-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L227-L236

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

theorem GroundTheory.Global.Elliptic.hasSum_weierstrassP_laurent {z : ℂ} (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖) :
    HasSum (fun j ↦ weierstrassLaurentCoeff L j * z ^ j) (℘[L] z - 1 / z ^ 2) := by sorry
