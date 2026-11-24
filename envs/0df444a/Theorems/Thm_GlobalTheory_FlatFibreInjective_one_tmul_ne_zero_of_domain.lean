-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreInjective_one_tmul_ne_zero_of_domain
-- name    : GlobalTheory.FlatFibreInjective.one_tmul_ne_zero_of_domain
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:44.29229+00:00
-- url     : https://prove2.me/theorems/edc4b112-9981-4f2d-94e4-6f8ee223eab4
-- title:
--   Flat Fibre Injective: one tmul ne zero of domain
-- statement:
--   The Flat Fibre Injective construction uses the one tmul ne zero of domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L11-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct

theorem GlobalTheory.FlatFibreInjective.one_tmul_ne_zero_of_domain {A P k : Type} [CommRing A] [IsDomain A] [AddCommGroup P]
    [Module A P] [Field k] [Algebra A k] (hinj : Function.Injective (algebraMap A k)) (y : P)
    (hy : ∀ a : A, a • y = 0 → a = 0) : (1 : k) ⊗ₜ[A] y ≠ 0 := by sorry
