-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_meromorphicAt_eval
-- name    : GroundTheory.Global.Elliptic.meromorphicAt_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:41.120338+00:00
-- url     : https://prove2.me/theorems/0c30c209-0326-40c4-807c-fb5abe2135f4
-- title:
--   Elliptic: meromorphic At eval
-- statement:
--   The Elliptic construction uses the meromorphic At eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L15-L19

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

theorem GroundTheory.Global.Elliptic.meromorphicAt_eval {g : ℂ → ℂ} {x : ℂ} (hg : MeromorphicAt g x) (P : ℂ[X]) :
    MeromorphicAt (fun z ↦ P.eval (g z)) x := by sorry
