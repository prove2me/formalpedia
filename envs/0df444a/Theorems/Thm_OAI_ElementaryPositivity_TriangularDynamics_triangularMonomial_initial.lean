-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularMonomial_initial
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:45.315573+00:00
-- url     : https://prove2.me/theorems/68c9fd12-e1f1-4e4e-9b86-f0bd66233ae1
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularMonomialCriterion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularMonomialCriterion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma triangularMonomial_initial {N:ℕ} (f:ElementaryExpr N)
--       (d:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N) (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
--       (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
--       (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
--         triangularExpression f (includeVertices (pureAnchor ν))=if ν=(fun a=>(μ a:ℤ)) then 1 else 0) :
--       polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)=
--         coneThetaInitial (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
--           (triangularBase N) d (includeVertices (natAnchor μ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.simpleTotalTransport` (definitions bundle `OAIQ368Chrom008` of this split); `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr`, `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.GapIndex` and `OAI.ElementaryPositivity.TriangularDynamics.Vertex` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeExtension.includeVertices`, `OAI.ElementaryPositivity.QuantumTorus.coneThetaInitial`, `OAI.ElementaryPositivity.QuantumTorus.polynomialInitial`, `OAI.ElementaryPositivity.TriangularDynamics.extendedCoord`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.extendedRoots`, `OAI.ElementaryPositivity.TriangularDynamics.natAnchor`, `OAI.ElementaryPositivity.TriangularDynamics.pureAnchor`, `OAI.ElementaryPositivity.TriangularDynamics.triangularBase` and `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.monomial_producer_supported` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularMonomialCriterion.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial)

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
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1
local instance instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1_re605d5_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1_re605d5_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1_re605d5_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega_1
lemma triangularMonomial_initial {N:ℕ} (f:ElementaryExpr N)
    (d:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N) (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N))
    (hp:∀ν:Fin (n+1) → ℤ,(∀i:Fin n,ν i.succ ≤ ν i.castSucc) →
      triangularExpression f (includeVertices (pureAnchor ν))=if ν=(fun a=>(μ a:ℤ)) then 1 else 0) :
    polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression f)=
      coneThetaInitial (extendedOmega n) (extendedRoots n) (simpleTotalTransport (extendedOmega n) (extendedRoots n))
        (triangularBase N) d (includeVertices (natAnchor μ)) := by
  sorry
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
