-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_admissible_polynomial_expansion
-- name    : OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T20:19:13.823587+00:00
-- url     : https://prove2.me/theorems/90536805-2313-4af9-be28-5b14dc880d04
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion` of [lean/OAI/Combinatorics/Chromatic/Witness/ElementaryProductDegree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementaryProductDegree.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open Packets WallUnits`, `open scoped BigOperators`, `open Classical`, and `variable {n:ℕ} (G:NaturalUnitIntervalGraph n)`):
--
--   ```lean
--   lemma admissible_polynomial_expansion (r:ℕ) : G.inversionChromatic r=
--       ∑w:{w:Equiv.Perm (Fin n) // G.Admissible w},
--         MvPolynomial.C (Polynomial.X^G.graphInversions w.val)*
--           MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (admissiblePartition G w)
--   ```
--
--   **In words.** For every `r : ℕ`, the statement says that `G.inversionChromatic r` equals the sum, over the permutations `w` of `Fin n` that are `G.Admissible`, of `MvPolynomial.C (Polynomial.X^G.graphInversions w.val)` times `MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (admissiblePartition G w)`.
--
--   **Definitions.** The statement uses `NaturalUnitIntervalGraph`, `inversionChromatic`, `Admissible`, `graphInversions` and `admissiblePartition`, written in the definitions bundles `OAIQ368Chrom060` of this split and in the shared definitions file Def_ElementaryPositivity.
--
--   **Used by.** Its proof file imports the published statement `OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive` of this split.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementaryProductDegree.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion)

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom060

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Packets WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma admissible_polynomial_expansion (r:ℕ) : G.inversionChromatic r=
    ∑w:{w:Equiv.Perm (Fin n) // G.Admissible w},
      MvPolynomial.C (Polynomial.X^G.graphInversions w.val)*
        MvPolynomial.esymmPart (Fin r) (Polynomial ℕ) (admissiblePartition G w) := by
  sorry
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
