-- Prove2me | Theorems.Thm_OAI_PiExponentJets_W22_homogeneous_local_regular_bezout_q68
-- name    : OAI.PiExponentJets.W22.homogeneous_local_regular_bezout_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:20:33.884868+00:00
-- url     : https://prove2.me/theorems/c46104ce-7c97-4da5-9a64-b83ad85ef50d
-- title:
--   OAI.PiExponentJets.W22.homogeneous_local_regular_bezout_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponentJets.W22.homogeneous_local_regular_bezout` of [lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousListHistory.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousListHistory.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponentJets.W22`, with `open PiExponentJets.W64`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem homogeneous_local_regular_bezout_q68
--       (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
--       (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
--       (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
--       (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
--         (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
--       (hlen : gs.length < Fintype.card σ)
--       (hT : T ∈ (Ideal.ofList gs).minimalPrimes) :
--       Module.length (Localization.AtPrime T)
--         (Localization.AtPrime T ⧸ (Ideal.ofList gs).map
--           (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))) ≤
--         ((∏ i ∈ Finset.range gs.length, degreeAt degrees i : ℕ) : ℕ∞)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponentJets.W64.degreeAt` (definitions bundle `OAIQ068A011` of this split).
--
--   **Used by.** The proof of `OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68` of this split imports it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousListHistory.lean (declaration OAI.PiExponentJets.W22.homogeneous_local_regular_bezout)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k]

variable [Fintype σ]

theorem homogeneous_local_regular_bezout_q68
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ)
    (hT : T ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime T)
      (Localization.AtPrime T ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))) ≤
      ((∏ i ∈ Finset.range gs.length, degreeAt degrees i : ℕ) : ℕ∞) := by
  sorry

end PiExponentJets.W22

end OAI
end
