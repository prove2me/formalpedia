-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_orbits_counting_principle_finite_fibres
-- name    : GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:33.367774+00:00
-- url     : https://prove2.me/theorems/ca314e56-99d1-4889-8ccc-ad0b77b5acaa
-- title:
--   T: finsum orbits counting principle finite fibres
-- statement:
--   The T construction uses the finsum orbits counting principle finite fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinsumOrbitsCountingPrincipleFiniteFibresStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinsumOrbitsCountingPrincipleFiniteFibresStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinsumOrbitsCountingPrincipleFiniteFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinsumOrbitsCountingPrincipleFiniteFibresStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finsum_orbits_counting_principle_finite_fibres : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by sorry
