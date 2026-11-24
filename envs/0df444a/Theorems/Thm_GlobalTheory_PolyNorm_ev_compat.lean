-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_ev_compat
-- name    : GlobalTheory.PolyNorm.ev_compat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:50:42.867393+00:00
-- url     : https://prove2.me/theorems/de40bdd8-bc4f-4ef8-881f-eb1dbb1aad88
-- title:
--   Poly Norm: ev compat
-- statement:
--   The Poly Norm construction uses the ev compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L136-L140

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

theorem GlobalTheory.PolyNorm.ev_compat (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K]
    [Algebra ℚ K] (s : ℕ) (F : K[X]) (hF : F.natDegree < s) :
    ev (Φ s) F = ev (Φ (F.natDegree + 1)) F := by sorry
