-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
-- name    : GlobalTheory.QCoh.Qcqs.exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:22.865341+00:00
-- url     : https://prove2.me/theorems/36a85a53-c085-4080-a4b2-4d2c95749767
-- title:
--   Qcqs: exists smul eq map of is Compact of is Quasi Separated
-- statement:
--   The Qcqs construction uses the exists smul eq map of is Compact of is Quasi Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L47-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L47-L92

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

theorem GlobalTheory.QCoh.Qcqs.exists_smul_eq_map_of_isCompact_of_isQuasiSeparated
    (hφ : ∀ {V W} (h : V ≤ W) (a : A W), φ V (rA h a) = rB h (φ W a))
    (hrB : ∀ {V₁ V₂ V₃} (h : V₁ ≤ V₂) (h' : V₂ ≤ V₃) (b : B V₃),
      rB h (rB h' b) = rB (h.trans h') b)
    (hbotA : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (A V))
    (hbotB : ∀ V : Set.Iic U, V.1 = ⊥ → Subsingleton (B V))
    (sepA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ a : A W, rA h₁ a = 0 → rA h₂ a = 0 → a = 0)
    (sepB : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ b : B W, rB h₁ b = 0 → rB h₂ b = 0 → b = 0)
    (glueA : ∀ {V₁ V₂ W : Set.Iic U} (h₁ : V₁ ≤ W) (h₂ : V₂ ≤ W), W.1 ≤ V₁.1 ⊔ V₂.1 →
      ∀ (a₁ : A V₁) (a₂ : A V₂), rA (inf_le_left : V₁ ⊓ V₂ ≤ V₁) a₁ = rA inf_le_right a₂ →
        ∃ a : A W, rA h₁ a = a₁ ∧ rA h₂ a = a₂)
    (hker : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ a : A V, φ V a = 0 → ∃ s ∈ S, s • a = 0)
    (hsurj : ∀ V : Set.Iic U, IsAffineOpen V.1 → ∀ b : B V, ∃ s ∈ S, ∃ a : A V, s • b = φ V a)
    (W : Set.Iic U) (hW : IsCompact (W.1 : Set X)) (hW' : IsQuasiSeparated (W.1 : Set X))
    (b : B W) : ∃ s ∈ S, ∃ a : A W, s • b = φ W a := by sorry
