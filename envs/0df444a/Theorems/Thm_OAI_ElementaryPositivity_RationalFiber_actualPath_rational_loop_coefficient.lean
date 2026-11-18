-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RationalFiber_actualPath_rational_loop_coefficient
-- name    : OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:57:09.077552+00:00
-- url     : https://prove2.me/theorems/3b24d378-44bc-4924-987a-94cc9bc73ff0
-- title:
--   OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient` of [lean/OAI/Combinatorics/Chromatic/Walls/PathOldTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PathOldTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RationalFiber`, with `open QuantumTorus PowerSeries WallUnits FiniteRayGeometry`):
--
--   ```lean
--   theorem actualPath_rational_loop_coefficient {a : Module.Dual ℝ E}
--       (p : GenericLinePath C e a a) (D : ℕ)
--       (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
--         (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
--       coeff D (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
--         (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
--         (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p
--           (max 1 ((mutationSize Ω C pc+1)*D))) f)=coeff D f
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.GenericLinePath`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.mutationSize`, `OAI.ElementaryPositivity.QuantumTorus.nonpDegree`, `OAI.ElementaryPositivity.QuantumTorus.pureDegree`, `OAI.ElementaryPositivity.QuantumTorus.simpleRoot`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus`, `OAI.ElementaryPositivity.RationalFiber.complementAlpha`, `OAI.ElementaryPositivity.RationalFiber.complementOmega`, `OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.RationalFiber.pureDegree_simple_self` (definitions bundle `OAIQ368Chrom005` of this split); `OAI.ElementaryPositivity.RationalFiber.actualPathWord` and `OAI.ElementaryPositivity.RationalFiber.comparisonWordAction` (definitions bundle `OAIQ368Chrom008` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RationalFiber.actualInfinityPath_loop_commute` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/PathOldTransport.lean (declaration OAI.ElementaryPositivity.RationalFiber.actualPath_rational_loop_coefficient)

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

include he hdeg in
theorem actualPath_rational_loop_coefficient {a : Module.Dual ℝ E}
    (p : GenericLinePath C e a a) (D : ℕ)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    coeff D (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p
        (max 1 ((mutationSize Ω C pc+1)*D))) f)=coeff D f := by
  sorry
end
end ElementaryPositivity.RationalFiber

end

end OAI
end
