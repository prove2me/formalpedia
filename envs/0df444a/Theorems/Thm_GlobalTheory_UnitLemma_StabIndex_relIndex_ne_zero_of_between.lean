-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_StabIndex_relIndex_ne_zero_of_between
-- name    : GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero_of_between
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:06.553158+00:00
-- url     : https://prove2.me/theorems/b1c4a2b1-09b1-49c9-aff9-13c375522b53
-- title:
--   Stab Index: rel Index ne zero of between
-- statement:
--   The Stab Index construction uses the rel Index ne zero of between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelIndexNeZeroOfBetween.lean#L43-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RelIndexNeZeroOfBetween.lean#L43-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexNeZeroOfBetween
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.StabIndex

theorem GlobalTheory.UnitLemma.StabIndex.relIndex_ne_zero_of_between (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A) (c : K.O) (hc : c ≠ 0)
    (hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite)
    (h : ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) :
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by sorry
