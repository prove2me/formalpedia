-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularPower_incoming_retain
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:14.845259+00:00
-- url     : https://prove2.me/theorems/6c69e93a-ca3f-44a6-9a3f-a5f5d00cb7c3
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain` of [lean/OAI/Combinatorics/Chromatic/Walls/LaurentPositiveDomination.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/LaurentPositiveDomination.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma triangularPower_incoming_retain (N:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N)
--       (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (d:ℕ)
--       (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N)) (k:ℕ) :
--       TorusPositive (extendedOmega n)
--         (sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
--           (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) k
--           (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression (linearPower N)))-
--           coneDelta (extendedOmega n) d (includeVertices (natAnchor μ)) k)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.simpleTotalTransport` (definitions bundle `OAIQ368Chrom008` of this split); `OAI.ElementaryPositivity.QuantumTorus.TorusPositive` and `OAI.ElementaryPositivity.QuantumTorus.sectionIncoming` (definitions bundle `OAIQ368Chrom013` of this split); `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.GapIndex` and `OAI.ElementaryPositivity.TriangularDynamics.Vertex` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeExtension.includeVertices`, `OAI.ElementaryPositivity.QuantumTorus.coneDelta`, `OAI.ElementaryPositivity.QuantumTorus.polynomialInitial`, `OAI.ElementaryPositivity.TriangularDynamics.extendedCoord`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.extendedRoots`, `OAI.ElementaryPositivity.TriangularDynamics.instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.linearPower`, `OAI.ElementaryPositivity.TriangularDynamics.natAnchor`, `OAI.ElementaryPositivity.TriangularDynamics.triangularBase` and `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial` and `OAI_ElementaryPositivity_TriangularDynamics_triangularTheta_support` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/LaurentPositiveDomination.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain)

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
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instRingTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instAddCommMonoidTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instAddCommGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instAddGroupTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.instSubTorusLaurentSeriesRatExtendedVertexCellVUnitExtendedOmega
lemma triangularPower_incoming_retain (N:ℕ) (μ:Fin (n+1) → ℕ) (hμ:∑a,μ a=N)
    (hdom:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (d:ℕ)
    (hm:HasRootDegree (extendedRoots n) d (includeVertices (natAnchor μ)-triangularBase N)) (k:ℕ) :
    TorusPositive (extendedOmega n)
      (sectionIncoming LaurentRay.vUnit (extendedOmega n) (extendedRoots n)
        (simpleTotalTransport (extendedOmega n) (extendedRoots n)) (triangularBase N) k
        (polynomialInitial (extendedOmega n) (extendedRoots n) (extendedCoord n) (triangularExpression (linearPower N)))-
        coneDelta (extendedOmega n) d (includeVertices (natAnchor μ)) k) := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
