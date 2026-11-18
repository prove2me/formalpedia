-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_QuantumTorus_literal_isotropic_adjoint
-- name    : OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:06:43.823265+00:00
-- url     : https://prove2.me/theorems/cbf7ec72-b321-4d57-8b05-76233194a694
-- title:
--   OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint` of [lean/OAI/Combinatorics/Chromatic/Walls/IsotropicLiteralPositive.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/IsotropicLiteralPositive.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.QuantumTorus`, with `open WeightedTorusSeries WallUnits PowerSeries`):
--
--   ```lean
--   lemma literal_isotropic_adjoint {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
--       (hF : F∈literalRootProducts Ω C (fun p=>p∈V)) :
--       (∀m,(∀p∈V,0≤Ω p m)→IntegralPositive Ω
--         (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
--       (∀m,(∀p∈V,Ω p m≤0)→IntegralPositive Ω
--         (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.literalRootProducts`, `OAI.ElementaryPositivity.QuantumTorus.Torus.X`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.IntegralPositive` (definitions bundle `OAIQ368Chrom013` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.QuantumTorus.positive_sections` and `OAI.ElementaryPositivity.QuantumTorus.section_line_program` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/IsotropicLiteralPositive.lean (declaration OAI.ElementaryPositivity.QuantumTorus.literal_isotropic_adjoint)

import Mathlib
import Definitions.Def_OAIQ368Chrom013

section

attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (V : AddSubmonoid M)
variable (hΩ : ∀p,Ω p p=0) (hV : ∀p∈V,∀q∈V,Ω p q=0)
include hΩ hV in
lemma literal_isotropic_adjoint {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C (fun p=>p∈V)) :
    (∀m,(∀p∈V,0≤Ω p m)→IntegralPositive Ω
      (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
    (∀m,(∀p∈V,Ω p m≤0)→IntegralPositive Ω
      (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F)) := by
  sorry
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end
