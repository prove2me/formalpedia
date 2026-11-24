-- Prove2me | Theorems.Thm_GlobalTheory_finiteAbelian_weightDecomposition
-- name    : GlobalTheory.finiteAbelian_weightDecomposition
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:13.794681+00:00
-- url     : https://prove2.me/theorems/a05edb9c-ee13-426f-aadb-28dbfa032af5
-- title:
--   Global Theory: finite Abelian weight Decomposition
-- statement:
--   The Global Theory construction uses the finite Abelian weight Decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L97-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L97-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open FiniteAbelianWeights

theorem GlobalTheory.finiteAbelian_weightDecomposition :
    ∀ (o : Type) [CommRing o] [IsDomain o] (N : ℕ) (ζ : o), 0 < N → IsUnit (N : o) →
    IsPrimitiveRoot ζ N → ∀ (T : Type) [CommGroup T] [Finite T], (∀ t : T, t ^ N = 1) →
    ∀ (M : Type) [AddCommGroup M] [Module o M] (ρ : Representation o T M)
      [DecidableEq (T →* oˣ)],
      Finite (T →* oˣ) ∧
      DirectSum.IsInternal
        (fun c : T →* oˣ => ⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)) ∧
      (∀ (T' : Subgroup T) (c' : T' →* oˣ),
        (⨅ t : T', LinearMap.ker (ρ t - (c' t : o) • LinearMap.id)) =
          ⨆ c : {c : T →* oˣ // c.comp T'.subtype = c'},
            ⨅ t, LinearMap.ker (ρ t - (c.1 t : o) • LinearMap.id)) ∧
      ∀ (A : Type) [CommRing A] [Algebra o A] (c : T →* oˣ),
        (⨅ t, LinearMap.ker ((ρ t).baseChange A - (algebraMap o A (c t)) • LinearMap.id)) =
          (⨅ t, LinearMap.ker (ρ t - (c t : o) • LinearMap.id)).baseChange A := by sorry
