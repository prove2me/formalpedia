-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W22_affine_local_regular_list_bezout_q68
-- name    : OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:13:28.577866+00:00
-- url     : https://prove2.me/theorems/6bc93777-b2fe-43d1-828b-95be1ed25842
-- title:
--   OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W22.affine_local_regular_list_bezout` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineLocalRegularBezout.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineLocalRegularBezout.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W22`, with `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem affine_local_regular_list_bezout_q68
--       {k : Type} [Field k] (n : ℕ)
--       (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
--       (gs : List (MvPolynomial (Fin n) k)) (D : ℕ)
--       (hdegree : ∀ g ∈ gs, g.totalDegree ≤ D)
--       (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
--         (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))))
--       (hlen : gs.length ≤ n) (hP : P ∈ (Ideal.ofList gs).minimalPrimes) :
--       Module.length (Localization.AtPrime P)
--         (Localization.AtPrime P ⧸ (Ideal.ofList gs).map
--           (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
--         ((D ^ gs.length : ℕ) : ℕ∞)
--   ```
--
--   **Used by.** The proof of `OAI.PiExponent.localIsolatedBezout_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineLocalRegularBezout.lean (declaration OAI.PiExponentJets.W22.affine_local_regular_list_bezout)

import Mathlib
import Lean.Elab.Tactic.Omega

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical

theorem affine_local_regular_list_bezout_q68
    {k : Type} [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (gs : List (MvPolynomial (Fin n) k)) (D : ℕ)
    (hdegree : ∀ g ∈ gs, g.totalDegree ≤ D)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))))
    (hlen : gs.length ≤ n) (hP : P ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ gs.length : ℕ) : ℕ∞) := by
  sorry

end PiExponentJets.W22

end OAI
end
