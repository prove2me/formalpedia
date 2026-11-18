-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_positive_sections
-- name    : OAI.ElementaryPositivity.QuantumTorus.positive_sections
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:06:35.407224+00:00
-- url     : https://prove2.me/theorems/4ab706b1-743e-4755-a55d-c19b2561dd21
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.positive_sections: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.positive_sections` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open PowerSeries PowerSeriesAdjoint PowerSeriesSplit FiniteRayGeometry FiniteEventTraversal LaurentPositive WallUnits`):
--
--   ```lean
--   theorem positive_sections (F : CompletedPositive LaurentRay.vUnit Ω C)
--       (incoming : PositiveIncomingPrescription Ω C F) (b : M)
--       (X : PowerSeries (Torus LaurentRay.vUnit Ω)) (hX : ShiftGraded LaurentRay.vUnit Ω C b X)
--       (hinc : ∀n,TorusPositive Ω (sectionIncoming LaurentRay.vUnit Ω C F b n X)) :
--       ∀N,∀h : Module.Dual ℝ E,TorusPositive Ω (coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.CompletedPositive`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.PositiveIncomingPrescription`, `OAI.ElementaryPositivity.QuantumTorus.ShiftGraded`, `OAI.ElementaryPositivity.QuantumTorus.TorusPositive`, `OAI.ElementaryPositivity.QuantumTorus.sectionIncoming` and `OAI.ElementaryPositivity.QuantumTorus.sectionValue` (definitions bundle `OAIQ368Chrom013` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive`, `OAI.ElementaryPositivity.TriangularDynamics.triangularMonomial_initial` and `OAI_ElementaryPositivity_TriangularDynamics_triangularTheta_support` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean (declaration OAI.ElementaryPositivity.QuantumTorus.positive_sections)

import Mathlib
import Definitions.Def_OAIQ368Chrom013

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

theorem positive_sections (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (b : M)
    (X : PowerSeries (Torus LaurentRay.vUnit Ω)) (hX : ShiftGraded LaurentRay.vUnit Ω C b X)
    (hinc : ∀n,TorusPositive Ω (sectionIncoming LaurentRay.vUnit Ω C F b n X)) :
    ∀N,∀h : Module.Dual ℝ E,TorusPositive Ω (coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X)) := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
