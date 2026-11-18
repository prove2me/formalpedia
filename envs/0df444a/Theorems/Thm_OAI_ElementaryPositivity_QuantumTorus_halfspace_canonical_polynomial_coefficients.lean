-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_halfspace_canonical_polynomial_coefficients
-- name    : OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:19:06.604245+00:00
-- url     : https://prove2.me/theorems/e24fca03-22f5-4a4c-9bea-19a11f3b5cdf
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients` of [lean/OAI/Combinatorics/Chromatic/GradedAlgebra/HalfspacePolynomialCoefficients.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/HalfspacePolynomialCoefficients.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint WallUnits FiniteRayGeometry`):
--
--   ```lean
--   lemma halfspace_canonical_polynomial_coefficients
--       (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
--       (pos:Bool) {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
--       (ha:cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
--       (hb:cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc))
--       (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
--         realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
--       (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
--         realMutationCovector e S (simpleRoot C pc) b (e m)≠0)
--       (F:Torus LaurentRay.vUnit Ω) (m:M) :
--       actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
--         (rootChartRatio Ω (mutatedRoots Ω C pc)
--           ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)
--           ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val
--         (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit F) (mutationLinearPiece Ω C pc pos m)=
--         actualPolynomialAdjointCoefficient Ω (rootOrder coord)
--           (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)).val F m
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.RegularCovector`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.actualPolynomialAdjointCoefficient`, `OAI.ElementaryPositivity.QuantumTorus.chartCompletionAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.cutSide`, `OAI.ElementaryPositivity.QuantumTorus.mutatedCoordinates`, `OAI.ElementaryPositivity.QuantumTorus.mutatedRoots`, `OAI.ElementaryPositivity.QuantumTorus.rootGrade`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instOne`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.realMutationCovector` and `OAI.ElementaryPositivity.QuantumTorus.rootOrder` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.QuantumTorus.mutationLinearPiece` (definitions bundle `OAIQ368Chrom003` of this split); `OAI.ElementaryPositivity.QuantumTorus.mutationTorusPush` and `OAI.ElementaryPositivity.QuantumTorus.wallRegradeRing` (definitions bundle `OAIQ368Chrom006` of this split); `OAI.ElementaryPositivity.QuantumTorus.rootChartRatio` (definitions bundle `OAIQ368Chrom008` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI_ElementaryPositivity_QuantumTorus_polynomialSection_mutation` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/GradedAlgebra/HalfspacePolynomialCoefficients.lean (declaration OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients)

import Mathlib
import Definitions.Def_OAIQ368Chrom008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits FiniteRayGeometry
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

attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.halfspacePolynomialCoefficientsRing
local instance halfspacePolynomialCoefficientsAddCommMonoid_r66b90a_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance halfspacePolynomialCoefficientsAddGroup_r66b90a_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd hcoord he hS hcomp hdeg in
lemma halfspace_canonical_polynomial_coefficients
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    (pos:Bool) {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:cutSide pos (a.toAddMonoidHom.comp e) (simpleRoot C pc))
    (hb:cutSide pos (b.toAddMonoidHom.comp e) (simpleRoot C pc))
    (ha':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) a (e m)≠0)
    (hb':∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) b (e m)≠0)
    (F:Torus LaurentRay.vUnit Ω) (m:M) :
    actualPolynomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (rootChartRatio Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) a).toAddMonoidHom.comp e)
        ((realMutationCovector e S (simpleRoot C pc) b).toAddMonoidHom.comp e)).val
      (mutationTorusPush Ω hΩ C pc pos LaurentRay.vUnit F) (mutationLinearPiece Ω C pc pos m)=
      actualPolynomialAdjointCoefficient Ω (rootOrder coord)
        (rootChartRatio Ω C (a.toAddMonoidHom.comp e) (b.toAddMonoidHom.comp e)).val F m := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
