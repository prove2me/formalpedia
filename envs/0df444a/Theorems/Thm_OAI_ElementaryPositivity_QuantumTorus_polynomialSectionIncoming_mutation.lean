-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_polynomialSectionIncoming_mutation
-- name    : OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:26:18.241817+00:00
-- url     : https://prove2.me/theorems/708f8e8f-b8ff-473e-9146-1fb4bdb50483
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` of [lean/OAI/Combinatorics/Chromatic/Walls/PolynomialIncomingProbes.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PolynomialIncomingProbes.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry`):
--
--   ```lean
--   lemma polynomialSectionIncoming_mutation (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
--       (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (r:M) :
--       polynomialSectionIncoming Ω C coord F r=
--         polynomialSectionIncoming Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) F'
--           (mutationIncomingLabel Ω (simpleRoot C pc) r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.mutatedCoordinates`, `OAI.ElementaryPositivity.QuantumTorus.mutatedRoots`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.mutationIncomingLabel` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.QuantumTorus.PureInitialRelation` (definitions bundle `OAIQ368Chrom012` of this split); `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming` (definitions bundle `OAIQ368Chrom057` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PolynomialIncomingProbes.lean (declaration OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation)

import Mathlib
import Definitions.Def_OAIQ368Chrom057

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)
include he hdeg hS hcomp hnd in
lemma polynomialSectionIncoming_mutation (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (r:M) :
    polynomialSectionIncoming Ω C coord F r=
      polynomialSectionIncoming Ω (mutatedRoots Ω C pc) (mutatedCoordinates Ω C coord pc) F'
        (mutationIncomingLabel Ω (simpleRoot C pc) r) := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
