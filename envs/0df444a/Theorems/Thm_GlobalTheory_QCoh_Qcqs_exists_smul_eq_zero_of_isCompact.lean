-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_zero_of_isCompact
-- name    : GlobalTheory.QCoh.Qcqs.exists_smul_eq_zero_of_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:28.76798+00:00
-- url     : https://prove2.me/theorems/82a538ad-0bd1-4cd9-be7f-d0f9ee452039
-- title:
--   Qcqs: exists smul eq zero of is Compact
-- statement:
--   The Qcqs construction uses the exists smul eq zero of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L21-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L21-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} {R : Type*} [CommRing R] (S : Submonoid R) (U : X.Opens)
  {A B : Set.Iic U → Type*} [∀ V, AddCommGroup (A V)] [∀ V, Module R (A V)]
  [∀ V, AddCommGroup (B V)] [∀ V, Module R (B V)]
  (rA : ∀ {V W : Set.Iic U}, V ≤ W → A W →ₗ[R] A V)
  (rB : ∀ {V W : Set.Iic U}, V ≤ W → B W →ₗ[R] B V)
  (φ : ∀ V, A V →ₗ[R] B V)

theorem GlobalTheory.QCoh.Qcqs.exists_smul_eq_zero_of_isCompact
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hbot : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (a : A W) (ha : φ W a = 0) :
    ∃ s ∈ S, s • a = 0 := by sorry
