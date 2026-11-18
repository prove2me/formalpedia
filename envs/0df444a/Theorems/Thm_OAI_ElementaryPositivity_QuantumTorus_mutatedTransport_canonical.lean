-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_canonical
-- name    : OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:18:41.382119+00:00
-- url     : https://prove2.me/theorems/b86ab1c2-3fff-4d24-98df-119489f843d6
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical` of [lean/OAI/Combinatorics/Chromatic/QuantumTorus/MutatedSystemIdentification.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/MutatedSystemIdentification.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries WallUnits`):
--
--   ```lean
--   lemma mutatedTransport_canonical
--       (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
--       {x y:Module.Dual ℝ E} (HX:RegularCovector C e x) (HY:RegularCovector C e y)
--       (hx:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
--         realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
--       (hy:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
--         realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
--       (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
--         (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
--           ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
--           (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val *
--           invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
--           ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
--           (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.RegularCovector`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.chartCompletionAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.chartNegative`, `OAI.ElementaryPositivity.QuantumTorus.mutatedRoots`, `OAI.ElementaryPositivity.QuantumTorus.rootGrade`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instOne`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.realMutationCovector` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_14` (definitions bundle `OAIQ368Chrom006` of this split); `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport` and `OAI.ElementaryPositivity.QuantumTorus.simpleTotalTransport` (definitions bundle `OAIQ368Chrom008` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI_ElementaryPositivity_QuantumTorus_polynomialSection_mutation` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/MutatedSystemIdentification.lean (declaration OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical)

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
open PowerSeries WallUnits
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
attribute [local instance] OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_14
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_17_r2c298f_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_17_r2c298f_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include hnd in
lemma mutatedTransport_canonical
    (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {x y:Module.Dual ℝ E} (HX:RegularCovector C e x) (HY:RegularCovector C e y)
    (hx:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) x (e m)≠0)
    (hy:∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m →
      realMutationCovector e S (simpleRoot C pc) y (e m)≠0) :
    (mutatedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HX HY).val=
      (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) y).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val *
        invOfUnit (chartNegative LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
        ((realMutationCovector e S (simpleRoot C pc) x).toAddMonoidHom.comp e)
        (simpleTotalTransport Ω (mutatedRoots Ω C pc))).val 1 := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
