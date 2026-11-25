-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_finiteEtale_open_closed_conditions
-- name    : GlobalTheory.FinEt.finiteEtale_open_closed_conditions
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:47.639479+00:00
-- url     : https://prove2.me/theorems/c75a7f72-9ce3-52f4-9ee6-0a8e103b2a1c
-- title:
--   Fin Et: finite Etale open closed conditions
-- statement:
--   The Fin Et construction uses the finite Etale open closed conditions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L716-L740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L716-L740

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.FinEt.finiteEtale_open_closed_conditions {S : Scheme.{u}} (X Y : Over S)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    (∀ f : X ⟶ Y, (IsFinite f.left ∧ Etale f.left) ∧ IsClopen (isoLocus f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ S), IsIso ((Over.pullback t).map f) ↔
        ∃ t' : T ⟶ isoLocusOpen f, t' ≫ (isoLocusOpen f).ι = t) ∧
      (IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k],
        Function.Bijective fun x : Spec (.of k) ⟶ X.left ↦ x ≫ f.left)) ∧
    (∀ f g : X ⟶ Y, IsClopen (eqLocus f g) ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ S), (Over.pullback t).map f = (Over.pullback t).map g ↔
        ∃ t' : T ⟶ eqLocusOpen f g, t' ≫ (eqLocusOpen f g).ι = t) ∧
    (∀ (k : Type u) [Field k] [IsSepClosed k], Nonempty (S ≅ Spec (.of k)) →
      ∃ n, IsSplitOfRank X.hom n) ∧
    (∀ n : ℕ, (∀ s, X.hom.finrank s = n) → ∃ (S' : Scheme.{u}) (t : S' ⟶ S),
      IsFinite t ∧ Etale t ∧ Surjective t ∧ IsSplitOfRank (pullback.snd X.hom t) n) := by sorry
