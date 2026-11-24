-- Prove2me | Theorems.Thm_GlobalTheory_FlatFibreInjective_exists_of_torsion
-- name    : GlobalTheory.FlatFibreInjective.exists_of_torsion
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:40.329393+00:00
-- url     : https://prove2.me/theorems/30fe5c79-f044-4539-bc82-9128a4b18f7b
-- title:
--   Flat Fibre Injective: exists of torsion
-- statement:
--   The Flat Fibre Injective construction uses the exists of torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L77-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/OneTmulNeZeroOfDomain.lean#L77-L100

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

theorem GlobalTheory.FlatFibreInjective.exists_of_torsion {R₀ N C : Type} [CommRing R₀] [AddCommGroup N] [Module R₀ N]
    [AddCommGroup C] [Module R₀ C] [Module.Flat R₀ C] (p : Ideal R₀) (hp : p.FG)
    (x : N ⊗[R₀] C) (hx : ∀ a ∈ p, a • x = 0) :
    ∃ y, (Submodule.torsionBySet R₀ N p).subtype.rTensor C y = x := by sorry
