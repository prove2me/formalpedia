-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_algHom_ker_eq_of_isMaximal
-- name    : GlobalTheory.OnePoint.exists_algHom_ker_eq_of_isMaximal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:44.1978+00:00
-- url     : https://prove2.me/theorems/c14688f8-5ab6-42f8-afce-53e00ade6285
-- title:
--   One Point: exists alg Hom ker eq of is Maximal
-- statement:
--   The One Point construction uses the exists alg Hom ker eq of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L14-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]

theorem GlobalTheory.OnePoint.exists_algHom_ker_eq_of_isMaximal {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (m : Ideal A) [m.IsMaximal] : ∃ φ : A →ₐ[K] Ω, RingHom.ker φ = m := by sorry
