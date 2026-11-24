-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreInjective_one_tmul_ne_zero
-- name    : GlobalTheory.FlatFibreInjective.one_tmul_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:56.688801+00:00
-- url     : https://prove2.me/theorems/e9542af7-2003-4e0f-805e-4debcc320fed
-- title:
--   Flat Fibre Injective: one tmul ne zero
-- statement:
--   The Flat Fibre Injective construction uses the one tmul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L32-L55

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

theorem GlobalTheory.FlatFibreInjective.one_tmul_ne_zero {R₀ P k : Type} [CommRing R₀] [AddCommGroup P] [Module R₀ P]
    [Field k] [Algebra R₀ k] (p : Ideal R₀) (hk : ∀ a, algebraMap R₀ k a = 0 ↔ a ∈ p)
    (hP : Module.IsTorsionBySet R₀ P p) (y : P) (hy : ∀ a : R₀, a • y = 0 → a ∈ p) :
    (1 : k) ⊗ₜ[R₀] y ≠ 0 := by sorry
