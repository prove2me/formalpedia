-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_degree
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T08:50:03.185839+00:00
-- url     : https://prove2.me/theorems/f254e7d1-01d9-4001-ba90-3e51201a1071
-- title:
--   Logarithmic frame words preserve weighted support degree
-- statement:
--   Applying any logarithmic frame word to a polynomial preserves its weighted support-degree bound. The positive support weights ensure differentiation cannot increase weighted degree, while the distinguished Euler term preserves its exponent.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (hc : ∀ i : Fin m, Function.Injective (fun j : Fin K => c j i))
    (hm : 1 ≤ m) (hK : 1 ≤ K)
    (w v : Fin (m + 1) → Rat)
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (N M : Real) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (F : MvPolynomial (Fin (m + 1)) Complex)
    (hF : logarithmicDegreeBound w N F)
    (hjet : logarithmicJetBound c v M F)
    (word : List (Fin (m + 1)))
    (hword : logarithmicFrameCost v word ≤ M) :
    logarithmicDegreeBound w N (logarithmicFrameWord word F) := by sorry
