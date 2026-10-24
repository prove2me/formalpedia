-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_frame_word_preserves_degree_and_jets
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree_and_jets
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T08:42:35.95689+00:00
-- url     : https://prove2.me/theorems/e88166c1-b117-4238-8ae8-7503be8d5cc6
-- title:
--   Logarithmic frame words preserve degree and spend jet weight
-- statement:
--   For positive weights, applying a logarithmic frame word preserves the weighted support-degree bound and lowers the formal jet threshold by at most the sum of the letter weights. The word-cost hypothesis ensures the retained threshold is nonnegative. An independent proof route is induction on the word, proving the one-letter degree and jet estimates from the definitions of the frame derivative and formal jet, then composing them.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmic_frame_word_preserves_degree_and_jets
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
    logarithmicDegreeBound w N (logarithmicFrameWord word F) ∧
      logarithmicJetBound c v (M - logarithmicFrameCost v word)
        (logarithmicFrameWord word F) := by sorry
