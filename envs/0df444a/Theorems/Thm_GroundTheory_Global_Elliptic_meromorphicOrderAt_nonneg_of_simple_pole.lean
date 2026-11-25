-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_meromorphicOrderAt_nonneg_of_simple_pole
-- name    : GroundTheory.Global.Elliptic.meromorphicOrderAt_nonneg_of_simple_pole
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:51:18.610877+00:00
-- url     : https://prove2.me/theorems/5c185190-ba93-4787-ace8-020da3a9b0ef
-- title:
--   Elliptic: meromorphic Order At nonneg of simple pole
-- statement:
--   The Elliptic construction uses the meromorphic Order At nonneg of simple pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L67-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L67-L91

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
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
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.meromorphicOrderAt_nonneg_of_simple_pole {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    {p : ℂ} (hp : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p)
    (ho : ∀ z, z - p ∉ L.lattice → 0 ≤ meromorphicOrderAt f z) (z : ℂ) :
    0 ≤ meromorphicOrderAt f z := by sorry
