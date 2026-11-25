-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_exists_polynomial_of_even_of_analyticAt_off_lattice
-- name    : GroundTheory.Global.Elliptic.exists_polynomial_of_even_of_analyticAt_off_lattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:01.740545+00:00
-- url     : https://prove2.me/theorems/e94a22dd-1430-4203-8c10-4672f51bf2a2
-- title:
--   Elliptic: exists polynomial of even of analytic At off lattice
-- statement:
--   The Elliptic construction uses the exists polynomial of even of analytic At off lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L127-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean#L127-L176

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

theorem GroundTheory.Global.Elliptic.exists_polynomial_of_even_of_analyticAt_off_lattice (n : ℕ) {g : ℂ → ℂ}
    (hg : Meromorphic g) (hp : IsPeriodic L g) (he : ∀ z, g (-z) = g z)
    (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (hn : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g 0) :
    ∃ P : ℂ[X], g =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) := by sorry
