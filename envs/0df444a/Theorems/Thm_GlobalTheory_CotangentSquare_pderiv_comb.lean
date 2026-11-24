-- Prove2me | Theorems.Thm_GlobalTheory_CotangentSquare_pderiv_comb
-- name    : GlobalTheory.CotangentSquare.pderiv_comb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:48.483059+00:00
-- url     : https://prove2.me/theorems/057f9077-0c53-437a-84e1-57068ba178e7
-- title:
--   Cotangent Square: pderiv comb
-- statement:
--   The Cotangent Square construction uses the pderiv comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CotangentMapInjectiveOfSquarePresentationAtPoint.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CotangentMapInjectiveOfSquarePresentationAtPoint.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.CotangentSquare
open MvPolynomial
variable {O B σ : Type} [CommRing O] [CommRing B]

theorem GlobalTheory.CotangentSquare.pderiv_comb [Fintype σ] (η : MvPolynomial σ B →+* O) (f g : σ → MvPolynomial σ B)
    (hf : ∀ i, η (f i) = 0) (k : MvPolynomial σ B) (hk : k ∈ firstOrderKer η) (l : σ) :
    η (pderiv l (∑ i, g i * f i + k)) = ∑ i, η (g i) * η (pderiv l (f i)) := by sorry
