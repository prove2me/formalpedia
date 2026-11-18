-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualInfinityPath_product_square
-- name    : OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:17:45.288469+00:00
-- url     : https://prove2.me/theorems/8c40e27c-a792-44fb-ac43-453ddf02b293
-- title:
--   OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square` of [lean/OAI/Combinatorics/Chromatic/Walls/InfinityPath.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/InfinityPath.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RationalFiber`, with `open QuantumTorus PowerSeries WallUnits FiniteRayGeometry`):
--
--   ```lean
--   lemma actualInfinityPath_product_square {a b : Module.Dual ℝ E}
--       (p : GenericLinePath C e a b) (N : ℕ) (hN : 1≤N)
--       (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
--         (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
--       innerHom (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N)
--         (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
--           (decide (0<a (e (simpleRoot C pc)))) x)=
--       infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
--         (decide (0<b (e (simpleRoot C pc))))
--         (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
--           (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
--           (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.mutationSize`, `OAI.ElementaryPositivity.QuantumTorus.nonpDegree`, `OAI.ElementaryPositivity.QuantumTorus.pureDegree`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus`, `OAI.ElementaryPositivity.RationalFiber.complementAlpha`, `OAI.ElementaryPositivity.RationalFiber.complementOmega`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.RationalFiber.innerHom` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.RationalFiber.pureDegree_simple_self` (definitions bundle `OAIQ368Chrom005` of this split); `OAI.ElementaryPositivity.RationalFiber.infinitySideHom`, `OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_6` and `OAI.ElementaryPositivity.RationalFiber.instRingTorus_13` (definitions bundle `OAIQ368Chrom006` of this split); `OAI.ElementaryPositivity.RationalFiber.actualInfinityPathProductUnit`, `OAI.ElementaryPositivity.RationalFiber.actualPathWord` and `OAI.ElementaryPositivity.RationalFiber.comparisonWordAction` (definitions bundle `OAIQ368Chrom008` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.halfspace_canonical_polynomial_coefficients`, `OAI.ElementaryPositivity.QuantumTorus.mutatedIncoming_probe`, `OAI.ElementaryPositivity.QuantumTorus.mutatedTransport_canonical`, `OAI_ElementaryPositivity_QuantumTorus_mutatedTransport_eq_path`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/InfinityPath.lean (declaration OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_product_square)

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

attribute [local instance] OAI.ElementaryPositivity.RationalFiber.instRingTorusLaurentSeriesRatVUnit_6
local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_6_r50e46d_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_6_r50e46d_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma actualInfinityPath_product_square {a b : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (N : ℕ) (hN : 1≤N)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityPathProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p N)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<a (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<b (e (simpleRoot C pc))))
      (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N) x) := by
  sorry
end
end ElementaryPositivity.RationalFiber

end

end OAI
end
