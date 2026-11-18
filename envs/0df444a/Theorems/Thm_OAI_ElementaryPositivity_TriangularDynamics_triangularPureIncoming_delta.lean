-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularPureIncoming_delta
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:36:41.323128+00:00
-- url     : https://prove2.me/theorems/aa553381-2ab8-44b6-9dab-26a59b58c278
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta` of [lean/OAI/Combinatorics/Chromatic/Walls/LaurentPositiveDomination.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/LaurentPositiveDomination.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension`, `open Classical`):
--
--   ```lean
--   lemma triangularPureIncoming_delta {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
--       (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
--       (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
--         triangularExpression f (includeVertices (pureAnchor ν))=if ν=μ then 1 else 0)
--       (ν:Fin (n+1) → ℤ) :
--       triangularIncoming f (pureAnchor ν)=if ν=μ then 1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.Torus` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr`, `OAI.ElementaryPositivity.TriangularDynamics.Cell` and `OAI.ElementaryPositivity.TriangularDynamics.Vertex` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeExtension.includeVertices`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.pureAnchor`, `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` and `OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proofs of `OAI_ElementaryPositivity_TriangularDynamics_triangularExpression_anchorSupported` and `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/LaurentPositiveDomination.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta)

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
open QuantumTorus WallUnits LatticeExtension
open Classical
noncomputable section
variable {n:ℕ}

lemma triangularPureIncoming_delta {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) → ℤ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
      triangularExpression f (includeVertices (pureAnchor ν))=if ν=μ then 1 else 0)
    (ν:Fin (n+1) → ℤ) :
    triangularIncoming f (pureAnchor ν)=if ν=μ then 1 else 0 := by
  sorry
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
