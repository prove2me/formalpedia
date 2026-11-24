-- Prove2me | Theorems.Thm_GlobalTheory_SemilocalBasis_exists_forall_notMem
-- name    : GlobalTheory.SemilocalBasis.exists_forall_notMem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:53:21.609155+00:00
-- url     : https://prove2.me/theorems/8b04c141-8050-4c36-b2bd-5d64777b4512
-- title:
--   Semilocal Basis: exists forall not Mem
-- statement:
--   The Semilocal Basis construction uses the exists forall not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L14-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsBasisMemOfSpanEqTopOfSemilocal.lean#L14-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal
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
open GlobalTheory
open GlobalTheory.SemilocalBasis
open scoped Pointwise

theorem GlobalTheory.SemilocalBasis.exists_forall_notMem {A V J : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [AddCommGroup V] [Module A V] [Finite J]
    (p : J → Submodule A V) (hp : ∀ i, p i ≠ ⊤)
    (hm : ∀ i, ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x, a • x ∈ p i) : ∃ x : V, ∀ i, x ∉ p i := by sorry
