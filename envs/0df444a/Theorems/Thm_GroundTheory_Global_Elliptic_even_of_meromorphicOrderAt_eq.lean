-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_even_of_meromorphicOrderAt_eq
-- name    : GroundTheory.Global.Elliptic.even_of_meromorphicOrderAt_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:37.907491+00:00
-- url     : https://prove2.me/theorems/cae52e47-b51c-49e9-9998-1070c84b3e66
-- title:
--   Elliptic: even of meromorphic Order At eq
-- statement:
--   The Elliptic construction uses the even of meromorphic Order At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L85-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L85-L115

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

theorem GroundTheory.Global.Elliptic.even_of_meromorphicOrderAt_eq {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (he : ∀ z, f (-z) = f z) {n : ℤ} (hn : meromorphicOrderAt f 0 = n) : Even n := by sorry
