-- Prove2me | Theorems.Thm_GlobalTheory_PointFunction_exists_eq_eval
-- name    : GlobalTheory.PointFunction.exists_eq_eval
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:34.975627+00:00
-- url     : https://prove2.me/theorems/e16b1008-6d53-4c7f-9e3c-cd4ca9d79dc1
-- title:
--   Point Function: exists eq eval
-- statement:
--   The Point Function construction uses the exists eq eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NonemptyAlgHomAlgebraicClosure.lean#L62-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NonemptyAlgHomAlgebraicClosure.lean#L62-L126

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

theorem GlobalTheory.PointFunction.exists_eq_eval (K : Type) [Field K] [CharZero K] (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra K A]
    (W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k], (A →ₐ[K] k) → k)
    (h1 : ∀ (k k' : Type) [Field k] [IsAlgClosed k] [Algebra K k] [Field k'] [IsAlgClosed k']
      [Algebra K k'] (φ : A →ₐ[K] k) (χ : k →ₐ[K] k'), W k' (χ.comp φ) = χ (W k φ))
    (h2 : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra K V],
      IsAlgClosed (FractionRing V) → ∀ ι : A →ₐ[K] V, ∃ v : V,
        ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : V →ₐ[K] k),
          W k (φ.comp ι) = φ v) :
    ∃ r : A, ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k] (φ : A →ₐ[K] k),
      W k φ = φ r := by sorry
