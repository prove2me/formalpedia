-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_monomial_producer_supported
-- name    : OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:02.642361+00:00
-- url     : https://prove2.me/theorems/23b1be3c-e00f-45ee-93a0-71ec90417ab7
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularAnchored.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularAnchored.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma monomial_producer_supported (μ : Fin (n+1) →₀ ℕ)
--       (hμ:∀i:Fin n, μ i.succ ≤ μ i.castSucc) :
--       ∃ f:ElementaryExpr μ.degree,
--         f.ordinary=(OrbitMonomial.polynomial μ : MvPolynomial (Fin (n+1)) ℤ) ∧
--         AnchorSupported (n:=n) f
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.OrbitMonomial.polynomial`, `OAI.ElementaryPositivity.TriangularDynamics.AnchorSupported` and `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.ordinary` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularAnchored.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported)

import Mathlib
import Definitions.Def_OAIQ368Chrom058

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n : ℕ}

lemma monomial_producer_supported (μ : Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n, μ i.succ ≤ μ i.castSucc) :
    ∃ f:ElementaryExpr μ.degree,
      f.ordinary=(OrbitMonomial.polynomial μ : MvPolynomial (Fin (n+1)) ℤ) ∧
      AnchorSupported (n:=n) f := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
