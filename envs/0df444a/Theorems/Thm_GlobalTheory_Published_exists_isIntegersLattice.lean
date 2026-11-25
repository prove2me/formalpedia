-- Prove2me | Theorems.Thm_GlobalTheory_Published_exists_isIntegersLattice
-- name    : GlobalTheory.Published.exists_isIntegersLattice
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:44.270623+00:00
-- url     : https://prove2.me/theorems/41db78ed-8e79-4dbe-8c78-61eb12c54d34
-- title:
--   Published: exists is Integers Lattice
-- statement:
--   The Published construction uses the exists is Integers Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L152-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L152-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ} {K : Type} [Field K] [NumberField K]
variable [Algebra K ℂ]

theorem GlobalTheory.Published.exists_isIntegersLattice (hp : 0 < p) : ∃ L, IsIntegersLattice p L := by sorry
