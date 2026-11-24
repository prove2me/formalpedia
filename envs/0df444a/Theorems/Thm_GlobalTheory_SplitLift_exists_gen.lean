-- Prove2me | Theorems.Thm_GlobalTheory_SplitLift_exists_gen
-- name    : GlobalTheory.SplitLift.exists_gen
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:43.52521+00:00
-- url     : https://prove2.me/theorems/3f660162-50ce-4857-b7fb-f09e5f1a867a
-- title:
--   Split Lift: exists gen
-- statement:
--   The Split Lift construction uses the exists gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L32-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L32-L79

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}

theorem GlobalTheory.SplitLift.exists_gen (S : Subring A) (Λ : Submodule S (Fin n → A)) {k : Type} [Field k]
    (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S) (hfg : Λ.FG)
    (hε : ε * ε = ε) (hrε : r ε = 1)
    (hr : Function.Surjective r) (hloc : ∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε)
    (hc : Function.Surjective c)
    (hker : ∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) :
    ∃ μ : Fin n → Λ, (∀ a : Fin n → S, c (∑ i, a i • μ i) = fun i => r (a i)) ∧
      (∀ i, ε • μ i = μ i) ∧ ∀ y : Λ, ∃ a : Fin n → S, ε • y = ∑ i, a i • μ i := by sorry
