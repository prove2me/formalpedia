-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_mem_pow_span
-- name    : GlobalTheory.eq_zero_of_mem_pow_span
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:03.232102+00:00
-- url     : https://prove2.me/theorems/8af93b68-0fa6-47a8-a1e6-34529c7cf456
-- title:
--   Global Theory: eq zero of mem pow span
-- statement:
--   The Global Theory construction uses the eq zero of mem pow span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroOfDvdPowUniformiser.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroOfDvdPowUniformiser.lean#L28-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroOfDvdPowUniformiser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.eq_zero_of_mem_pow_span {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) (x : X) (hx : x ∈ U) (a b : Γ(X, U)) (ha : x ∉ X.basicOpen a)
    (hb : ∀ e : ℕ, b ∈ Ideal.span {a} ^ e) : b = 0 := by sorry
