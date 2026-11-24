-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_graph_bijective
-- name    : GlobalTheory.FieldBaseChange.graph_bijective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:24.396811+00:00
-- url     : https://prove2.me/theorems/a9619bec-e1db-4b53-b05d-76a662cfaf78
-- title:
--   Field Base Change: graph bijective
-- statement:
--   The Field Base Change construction uses the graph bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L177-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L177-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]

theorem GlobalTheory.FieldBaseChange.graph_bijective (X : Submodule R (V₀ × ∀ j, P₀ j))
    (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : ∀ j, P₀ j →ₛₗ[algebraMap R K] P j)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] P' j) (hb : ∀ j, IsExtension (b j))
    (d : W →ₛₗ[algebraMap K F] W') (hd : IsExtension d)
    (π : ∀ j, W →ₗ[K] P j) (π' : ∀ j, W' →ₗ[F] P' j) (comm : ∀ j w, π' j (d w) = b j (π j w))
    (E : V → W → Prop)
    (hE : ∀ v w, E v w ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ X, ρ x.1 = algebraMap R K r • v ∧
      ∀ j, ρ' j (x.2 j) = algebraMap R K r • π j w)
    (bij : (∀ v, ∃! w, E v w) ∧ ∀ w, ∃! v, E v w)
    (E' : V' → W' → Prop)
    (hE' : ∀ v w, E' v w ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → V₀ × ∀ j, P₀ j), (∀ i, x i ∈ X) ∧
      v = ∑ i, c i • a (ρ (x i).1) ∧ ∀ j, π' j w = ∑ i, c i • b j (ρ' j ((x i).2 j))) :
    (∀ v, ∃! w, E' v w) ∧ ∀ w, ∃! v, E' v w := by sorry
