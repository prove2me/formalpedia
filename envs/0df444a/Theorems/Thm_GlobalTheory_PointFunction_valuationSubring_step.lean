-- Prove2me | Theorems.Thm_GlobalTheory_PointFunction_valuationSubring_step
-- name    : GlobalTheory.PointFunction.valuationSubring_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:28.706512+00:00
-- url     : https://prove2.me/theorems/893ac5ea-3ac0-486d-a786-adc2be0c83c0
-- title:
--   Point Function: valuation Subring step
-- statement:
--   The Point Function construction uses the valuation Subring step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NonemptyAlgHomAlgebraicClosure.lean#L29-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NonemptyAlgHomAlgebraicClosure.lean#L29-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NonemptyAlgHomAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PointFunction
open IsLocalRing

theorem GlobalTheory.PointFunction.valuationSubring_step (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (ι : A →ₐ[K] Ω)
    (V : ValuationSubring Ω) (h : ∀ a, ι a ∈ V) :
    W Ω ι ∈ V ∧ ∃ (_ : Algebra K (AlgebraicClosure (ResidueField V)))
      (φ : A →ₐ[K] AlgebraicClosure (ResidueField V)),
      (∀ a, φ a = 0 ↔ (⟨ι a, h a⟩ : V) ∈ maximalIdeal V) ∧
        ∀ r, ι r = W Ω ι → W _ φ = φ r := by sorry
