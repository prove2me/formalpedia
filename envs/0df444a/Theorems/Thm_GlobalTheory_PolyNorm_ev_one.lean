-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_ev_one
-- name    : GlobalTheory.PolyNorm.ev_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:48.359819+00:00
-- url     : https://prove2.me/theorems/248a1486-898c-48ad-a5aa-27b5190f4ffd
-- title:
--   Poly Norm: ev one
-- statement:
--   The Poly Norm construction uses the ev one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L130-L134

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

theorem GlobalTheory.PolyNorm.ev_one (h1 : N 1 = 1) {K : Type} [CommRing K] [Algebra ℚ K] (r : ℕ) :
    ev (Φ (r + 1)) (1 : K[X]) = 1 := by sorry
