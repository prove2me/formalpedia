-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_algHom_ker_eq_nilradical
-- name    : GlobalTheory.OnePoint.exists_algHom_ker_eq_nilradical
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:41.531847+00:00
-- url     : https://prove2.me/theorems/1bd9fef6-521e-4faa-92dd-172a7f007d41
-- title:
--   One Point: exists alg Hom ker eq nilradical
-- statement:
--   The One Point construction uses the exists alg Hom ker eq nilradical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L25-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L25-L53

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

theorem GlobalTheory.OnePoint.exists_algHom_ker_eq_nilradical [PerfectField K] {A : Type v} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Nontrivial A] (Ω : Type w) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : A →ₐ[K] Ω, a = b) : ∃ φ : A →ₐ[K] K, RingHom.ker φ = nilradical A := by sorry
