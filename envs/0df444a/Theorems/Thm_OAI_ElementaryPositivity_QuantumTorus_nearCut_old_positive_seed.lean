-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_nearCut_old_positive_seed
-- name    : OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:20:32.288211+00:00
-- url     : https://prove2.me/theorems/81f13666-06ae-4104-9613-f8927930e86d
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed` of [lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutPolynomialSeeds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutPolynomialSeeds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint WallUnits RationalFiber FiniteRayGeometry`):
--
--   ```lean
--   lemma nearCut_old_positive_seed (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
--       {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
--       (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
--       (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
--       (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
--       polynomialSectionCoefficient Ω C coord (b.toAddMonoidHom.comp e) F m=F' m
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.RegularCovector`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.NearCut`, `OAI.ElementaryPositivity.QuantumTorus.PureInitialRelation` and `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionCoefficient` (definitions bundle `OAIQ368Chrom012` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI_ElementaryPositivity_QuantumTorus_polynomialSection_mutation` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/QuantumTorus/NearCutPolynomialSeeds.lean (declaration OAI.ElementaryPositivity.QuantumTorus.nearCut_old_positive_seed)

import Mathlib
import Definitions.Def_OAIQ368Chrom012

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

local instance nearCutPolynomialSeedsRing_r7db970_1 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance nearCutPolynomialSeedsAddCommMonoid_r7db970_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance nearCutPolynomialSeedsAddGroup_r7db970_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
include he hdeg hS hcomp in
lemma nearCut_old_positive_seed (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc)))
    (F F':Torus LaurentRay.vUnit Ω) (hF:PureInitialRelation Ω hΩ C coord hcoord pc F F') (m:M) :
    polynomialSectionCoefficient Ω C coord (b.toAddMonoidHom.comp e) F m=F' m := by
  sorry

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
