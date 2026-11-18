-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_thetaValue_positive
-- name    : OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:08:45.138745+00:00
-- url     : https://prove2.me/theorems/0269694a-af38-4e4a-8364-7dcec6ee2c8f
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits`):
--
--   ```lean
--   theorem thetaValue_positive (F : CompletedPositive LaurentRay.vUnit Ω C)
--       (incoming : PositiveIncomingPrescription Ω C F) (b : M) (h : Module.Dual ℝ E) :
--       IntegralPositive Ω (thetaValue LaurentRay.vUnit Ω C F b (h.toAddMonoidHom.comp e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.CompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.IntegralPositive` and `OAI.ElementaryPositivity.QuantumTorus.PositiveIncomingPrescription` (definitions bundle `OAIQ368Chrom013` of this split); `OAI.ElementaryPositivity.QuantumTorus.thetaValue` (definitions bundle `OAIQ368Chrom016` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean (declaration OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive)

import Mathlib
import Definitions.Def_OAIQ368Chrom016

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

theorem thetaValue_positive (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (b : M) (h : Module.Dual ℝ E) :
    IntegralPositive Ω (thetaValue LaurentRay.vUnit Ω C F b (h.toAddMonoidHom.comp e)) := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
