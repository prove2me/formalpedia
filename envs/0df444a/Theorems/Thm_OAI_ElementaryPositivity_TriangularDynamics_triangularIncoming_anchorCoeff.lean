-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularIncoming_anchorCoeff
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:45.90419+00:00
-- url     : https://prove2.me/theorems/7a909f91-fbb1-4283-ac37-a661231544f9
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff` of [lean/OAI/Combinatorics/Chromatic/Histories/TriangularCommonHistory.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/TriangularCommonHistory.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma triangularIncoming_anchorCoeff {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) →₀ ℕ)
--       (hμ:∀i:Fin n,μ i.succ≤μ i.castSucc) :
--       polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
--         (triangularExpression f) (anchorExponent μ)=
--         (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff μ
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming`, `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.GapIndex` and `OAI.ElementaryPositivity.TriangularDynamics.Vertex` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.TriangularDynamics.anchorExponent`, `OAI.ElementaryPositivity.TriangularDynamics.extendedCoord`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.extendedRoots`, `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` and `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.ordinary` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/TriangularCommonHistory.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming_anchorCoeff)

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
variable {n:ℕ}

lemma triangularIncoming_anchorCoeff {N:ℕ} (f:ElementaryExpr N) (μ:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ≤μ i.castSucc) :
    polynomialSectionIncoming (extendedOmega n) (extendedRoots n) (extendedCoord n)
      (triangularExpression f) (anchorExponent μ)=
      (f.ordinary (σ:=Fin (n+1)) (R:=LaurentSeries ℚ)).coeff μ := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
