-- Prove2me | Theorems.Thm_GlobalTheory_UnitPairNorm_main_ind
-- name    : GlobalTheory.UnitPairNorm.main_ind
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:15.830574+00:00
-- url     : https://prove2.me/theorems/46ef9ae6-c3ce-4adb-aaba-721004e95a2a
-- title:
--   Unit Pair Norm: main ind
-- statement:
--   The Unit Pair Norm construction uses the main ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L152-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean#L152-L288

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [FiniteDimensional E V]

theorem GlobalTheory.UnitPairNorm.main_ind (c : E ≃+* E) (hcc : ∀ x, c (c x) = x)
    (hcint : ∀ x : O, ∃ y : O, c (algebraMap O E x) = algebraMap O E y)
    (hnorm : ∀ u : Oˣ, c (algebraMap O E u) = algebraMap O E u →
      ∃ z : Oˣ, algebraMap O E u = algebraMap O E z * c (algebraMap O E z))
    (hz : ∃ z : O, algebraMap O E z + c (algebraMap O E z) = 1)
    (h : V → V → E)
    (hadd : ∀ x y z : V, h (x + y) z = h x z + h y z)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (hsym : ∀ x y : V, h y x = c (h x y)) :
    ∀ (n : ℕ) (W : Submodule E V), finrank E W = n → ∀ L : Submodule O V, L.FG →
      Submodule.span E (L : Set V) = W →
      (∀ y ∈ W, (y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap O E).range)) →
      ∃ (m : ℕ) (v : Fin m → V), (∀ i j, h (v i) (v j) = if i = j then 1 else 0) ∧
        Submodule.span O (Set.range v) = L := by sorry
