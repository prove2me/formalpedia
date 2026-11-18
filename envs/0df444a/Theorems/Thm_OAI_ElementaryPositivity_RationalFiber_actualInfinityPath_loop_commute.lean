-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_loop_commute
-- name    : OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:56:51.244605+00:00
-- url     : https://prove2.me/theorems/a6c727eb-7d1d-4dce-b835-0b4b26f55c57
-- title:
--   OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute` of [lean/OAI/Combinatorics/Chromatic/Walls/InfinityFiniteLoop.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/InfinityFiniteLoop.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RationalFiber`, with `open QuantumTorus PowerSeries WallUnits FiniteRayGeometry`):
--
--   ```lean
--   lemma actualInfinityPath_loop_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
--       (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (m : M) :
--       coeff d ((actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val*
--         PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m)))=
--       coeff d (PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m))*
--         (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.mutationSize`, `OAI.ElementaryPositivity.QuantumTorus.pureDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus.X` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_6` and `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_7` (definitions bundle `OAIQ368Chrom006` of this split); `OAI.ElementaryPositivity.RationalFiber.actualInfinityPathProductUnit` (definitions bundle `OAIQ368Chrom008` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_negative_ratio` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/InfinityFiniteLoop.lean (declaration OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute)

import Mathlib
import Definitions.Def_OAIQ368Chrom008

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_7
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_7_radc960_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_7_radc960_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance instNonUnitalSemiringTorusLaurentSeriesRatVUnit_1_radc960_1 : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instNonUnitalNonAssocSemiringTorusLaurentSeriesRatVUnit_1
lemma actualInfinityPath_loop_commute {a : Module.Dual ℝ E} (p : GenericLinePath C e a a)
    (d N : ℕ) (hN : 1≤N) (hdN : (mutationSize Ω C pc+1)*d≤N) (m : M) :
    coeff d ((actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val*
      PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m)))=
    coeff d (PowerSeries.C (HahnSeries.single (-pureDegree coord pc m) (Torus.X LaurentRay.vUnit Ω m))*
      (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N).val) := by
  sorry

end
end ElementaryPositivity.RationalFiber

end

end OAI
end
