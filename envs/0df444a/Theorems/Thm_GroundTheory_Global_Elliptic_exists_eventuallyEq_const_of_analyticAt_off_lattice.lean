-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_exists_eventuallyEq_const_of_analyticAt_off_lattice
-- name    : GroundTheory.Global.Elliptic.exists_eventuallyEq_const_of_analyticAt_off_lattice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:44.328296+00:00
-- url     : https://prove2.me/theorems/29066698-5de1-4a08-b20e-b3b1e2bf2871
-- title:
--   Elliptic: exists eventually Eq const of analytic At off lattice
-- statement:
--   The Elliptic construction uses the exists eventually Eq const of analytic At off lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L117-L125

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

theorem GroundTheory.Global.Elliptic.exists_eventuallyEq_const_of_analyticAt_off_lattice {g : ℂ → ℂ} (hg : Meromorphic g)
    (hp : IsPeriodic L g) (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (h0 : 0 ≤ meromorphicOrderAt g 0) : ∃ c : ℂ, g =ᶠ[codiscrete ℂ] fun _ ↦ c := by sorry
