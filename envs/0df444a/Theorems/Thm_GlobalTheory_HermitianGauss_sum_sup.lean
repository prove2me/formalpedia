-- Prove2me | Theorems.Thm_GlobalTheory_HermitianGauss_sum_sup
-- name    : GlobalTheory.HermitianGauss.sum_sup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:19:42.645865+00:00
-- url     : https://prove2.me/theorems/3d5259d8-dc1f-4e99-8e97-73f18f2c2598
-- title:
--   Hermitian Gauss: sum sup
-- statement:
--   The Hermitian Gauss construction uses the sum sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L70-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussSumNondegenerateFiniteHermitianModule.lean#L70-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussSumNondegenerateFiniteHermitianModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.HermitianGauss
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]

theorem GlobalTheory.HermitianGauss.sum_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P)
    {A : Type} [AddCommMonoid A] (f : M → A) :
    ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y = ∑ q : R ⧸ P, ∑ d ∈ pts D, f (d + (Quotient.out q : R) • x) := by sorry
