-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero
-- name    : GroundTheory.Global.Elliptic.two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:05:27.800452+00:00
-- url     : https://prove2.me/theorems/799d31a0-47c3-5921-a640-bb5e494ef235
-- title:
--   Elliptic: two mul mem lattice iff deriv Weierstrass P eq zero
-- statement:
--   The Elliptic construction uses the two mul mem lattice iff deriv Weierstrass P eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Uniformization.lean#L128-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Uniformization.lean#L128-L141

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
variable {L}

theorem GroundTheory.Global.Elliptic.two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero {w : ℂ} (hw : w ∉ L.lattice) :
    2 * w ∈ L.lattice ↔ ℘'[L] w = 0 := by sorry
