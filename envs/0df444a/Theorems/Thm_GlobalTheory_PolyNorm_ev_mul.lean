-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_ev_mul
-- name    : GlobalTheory.PolyNorm.ev_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:37.785868+00:00
-- url     : https://prove2.me/theorems/4fe8bf69-7f75-4a0b-935e-45560f7dac55
-- title:
--   Poly Norm: ev mul
-- statement:
--   The Poly Norm construction uses the ev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L92-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L92-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN

theorem GlobalTheory.PolyNorm.ev_mul (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K] [Algebra ℚ K]
    (r₁ r₂ s : ℕ) (hs : r₁ + r₂ < s) (F G : K[X]) (hF : F.natDegree ≤ r₁)
    (hG : G.natDegree ≤ r₂) :
    ev (Φ s) (F * G) = ev (Φ (r₁ + 1)) F * ev (Φ (r₂ + 1)) G := by sorry
