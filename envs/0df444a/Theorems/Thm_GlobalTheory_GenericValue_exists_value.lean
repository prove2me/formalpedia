-- Prove2me | Theorems.Thm_GlobalTheory_GenericValue_exists_value
-- name    : GlobalTheory.GenericValue.exists_value
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:55:07.477034+00:00
-- url     : https://prove2.me/theorems/cfeccc7b-731d-4f30-accd-dd9d6de11935
-- title:
--   Generic Value: exists value
-- statement:
--   The Generic Value construction uses the exists value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomOfIsTranscendenceBasis.lean#L101-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomOfIsTranscendenceBasis.lean#L101-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomOfIsTranscendenceBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GenericValue
open MvPolynomial
variable {K : Type} [Field K]

theorem GlobalTheory.GenericValue.exists_value [IsAlgClosed K] {I : Type}
    (V : ∀ (R : Type) [CommRing R] [Algebra K R], (I → R) → R → Prop)
    (bc : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R']
      [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R') (T : I → R) (a : R), V R T a → V R' (j ∘ T) (j a))
    (uniq : ∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a a' : F), V F T a → V F T a' → a = a')
    (ex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T : I → Ω), AlgebraicIndependent K T → ∃ a, V Ω T a)
    (gg : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (T T' : I → Ω) (a a' : Ω),
      AlgebraicIndependent K (Sum.elim T T') → V Ω T a → V Ω T' a' → a = a')
    (lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω]
      [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω) (T : I → O) (a : Ω),
      RingHom.ker r = IsLocalRing.maximalIdeal O → V Ω (r ∘ T) a →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
        (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧ V O' (j ∘ T) u) :
    ∃ κ : K, (∀ (F : Type) [Field F] [Algebra K F] (T : I → F) (a : F), V F T a → a = algebraMap K F κ) ∧
      V (Gen K I) (genX K I) (algebraMap K _ κ) := by sorry
