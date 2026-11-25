-- Prove2me | Theorems.Thm_GlobalTheory_topFormOrd_vw_properties
-- name    : GlobalTheory.topFormOrd_vw_properties
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:24.474845+00:00
-- url     : https://prove2.me/theorems/d92c98cb-afde-4d7d-87cc-e82b57785259
-- title:
--   Global Theory: top Form Ord vw properties
-- statement:
--   The Global Theory construction uses the top Form Ord vw properties property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L602-L643
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L602-L643

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing

theorem GlobalTheory.topFormOrd_vw_properties (K V F : Type*) [Field K] [CharZero K] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra K V] [Algebra.EssFiniteType K V]
    [Algebra.FormallySmooth K V] [Field F] [Algebra V F] [IsFractionRing V F] [Algebra K F]
    [IsScalarTower K V F] {n : ℕ} (hn : Algebra.trdeg K F = n) :
    Algebra.trdeg K (ResidueField V) = (n - 1 : ℕ) ∧
    (∀ t : V, Irreducible t → ∃ (h : 0 < n) (z : Fin n → V) (b : Basis (Fin n) V Ω[V⁄K]),
      z ⟨0, h⟩ = t ∧ ∀ k, b k = D K V (z k)) ∧
    Nonempty (Basis (Fin n) V Ω[V⁄K]) ∧
    ∀ b : Basis (Fin n) V Ω[V⁄K],
      (∀ (b' : Basis (Fin n) V Ω[V⁄K]) (ω : ⋀[F]^n Ω[F⁄K]),
        topFormOrd_vw F b ω = topFormOrd_vw F b' ω) ∧
      (∀ ω : ⋀[F]^n Ω[F⁄K], ∃! f : F, ω = f • topFormGen F b) ∧
      (∀ f : F, topFormOrd_vw F b (f • topFormGen F b) = ordTop_vw V f) ∧
      (∀ x : Fin n → V, 0 ≤ topFormOrd_vw F b (dWedge K fun i => algebraMap V F (x i))) ∧
      (∀ (x : Fin n → V) (i j : Fin n), i ≠ j → x i ∈ maximalIdeal V → x j ∈ maximalIdeal V →
        1 ≤ topFormOrd_vw F b (dWedge K fun i => algebraMap V F (x i))) ∧
      (∀ (k : ℕ) (x : Fin n → F), (∀ i : Fin n, i.val < k → x i ≠ 0) →
        (∀ i : Fin n, k ≤ i.val → x i ∈ Set.range (algebraMap V F)) →
        ((-1 : ℤ) : WithTop ℤ) ≤ topFormOrd_vw F b (exteriorPower.ιMulti F n fun i =>
          if i.val < k then (x i)⁻¹ • D K F (x i) else D K F (x i))) ∧
      (∀ (k : ℕ) (x : Fin n → V), (∀ i : Fin n, i.val < k → IsUnit (x i)) →
        0 ≤ topFormOrd_vw F b (exteriorPower.ιMulti F n fun i =>
          if i.val < k then (algebraMap V F (x i))⁻¹ • D K F (algebraMap V F (x i))
          else D K F (algebraMap V F (x i)))) := by sorry
