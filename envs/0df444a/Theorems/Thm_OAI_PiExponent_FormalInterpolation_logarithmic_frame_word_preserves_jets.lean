-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_jets
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_jets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T08:50:24.949474+00:00
-- url     : https://prove2.me/theorems/87adbb93-8c99-4f7d-bd36-8abaf2241b01
-- title:
--   Logarithmic frame words spend their weighted jet cost
-- statement:
--   If a polynomial has no formal-jet coefficients below weighted threshold M, applying a frame word leaves no coefficients below M minus the word's total weight. The cost bound keeps that remaining threshold nonnegative.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_jets
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
    logarithmicJetBound c v (M - logarithmicFrameCost v word)
      (logarithmicFrameWord word F) := by sorry
