-- Prove2me | Theorems.Thm_GlobalTheory_BoundedBasis_pairing_injective
-- name    : GlobalTheory.BoundedBasis.pairing_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:02:18.45186+00:00
-- url     : https://prove2.me/theorems/af75752e-66c4-470f-b763-d3315c3e09ba
-- title:
--   Bounded Basis: pairing injective
-- statement:
--   The Bounded Basis construction uses the pairing injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L235-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetTypesOfBoundedBases.lean#L235-L248

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

theorem GlobalTheory.BoundedBasis.pairing_injective {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hi : LinearIndependent E v) : Function.Injective (pairing X v hv) := by sorry
