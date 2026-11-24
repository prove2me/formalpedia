-- Prove2me | Theorems.Thm_GlobalTheory_UnramSelfDual_exists_next
-- name    : GlobalTheory.UnramSelfDual.exists_next
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:47:06.556643+00:00
-- url     : https://prove2.me/theorems/7c8e6a3b-c89c-4133-ba9d-a0586a395221
-- title:
--   Unram Self Dual: exists next
-- statement:
--   The Unram Self Dual construction uses the exists next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L151-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsOfFixedInt.lean#L151-L271

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsSubConjNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_StabLatInfStabVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RestrHomSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsOfFixedInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal Formalism.UG
open GlobalTheory GlobalTheory.UnramSelfDual
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {O : Subalgebra R A}
  {c : A →+* A} {M : ℕ} {J : Matrix (Fin M) (Fin M) A} {L : Submodule O (Fin M → A)}

theorem GlobalTheory.UnramSelfDual.exists_next [Nontrivial A] (hc : ∀ a, c (c a) = a) (hJ : ∀ i j, c (J j i) = J i j)
    (hO : ∀ a ∈ O, c a ∈ O) {p q : A} (hp : p ∈ O) (hpc : c p = p) (hpq : p * q = 1)
    (hq : q ∉ O)
    (hloc : ∀ a ∈ O, c a = a → (∃ b ∈ O, a * b = 1) ∨ ∃ b ∈ O, a = p * b)
    (hθ : ∃ θ ∈ O, ∃ b ∈ O, (θ - c θ) * b = 1)
    (hnorm : ∀ a ∈ O, c a = a → (∃ b ∈ O, a * b = 1) → ∃ x ∈ O, c x * x = a)
    (hfg : L.FG) (hsp : Submodule.span A (L : Set (Fin M → A)) = ⊤)
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, hform c J z y ∈ O)
    {k : ℕ} (hk : k < M) {e : Fin k → Fin M → A} (heL : ∀ i, e i ∈ L)
    (he : ∀ i j, hform c J (e i) (e j) = if i = j then 1 else 0) :
    ∃ y ∈ L, (∀ i, hform c J (e i) y = 0) ∧ hform c J y y = 1 := by sorry
