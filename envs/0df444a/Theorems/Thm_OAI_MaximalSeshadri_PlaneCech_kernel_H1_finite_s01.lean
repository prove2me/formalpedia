-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PlaneCech_kernel_H1_finite_s01
-- name    : OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:16:56.425905+00:00
-- url     : https://prove2.me/theorems/5b895281-764f-4ea5-b7ff-eda04885de8c
-- title:
--   OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/KernelH1.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/KernelH1.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.PlaneCech`, with `open LaurentPlane`):
--
--   ```lean
--   theorem kernel_H1_finite_s01 (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
--       Module.Finite K ((cycles (K := K) (kernelA N) (kernelB N) (kernelC N d)) ⧸
--         fullBoundaries (K := K) (kernelA N) (kernelB N) (kernelC N d))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.LaurentPlane.Ring` and `OAI.MaximalSeshadri.PlaneCech.cycles` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.PlaneCech.fullBoundaries`, `OAI.MaximalSeshadri.PlaneCech.kernelA`, `OAI.MaximalSeshadri.PlaneCech.kernelB`, `OAI.MaximalSeshadri.PlaneCech.kernelC`, `OAI.MaximalSeshadri.PlaneCech.kernelCyclesAddCommGroup` and `OAI.MaximalSeshadri.PlaneCech.kernelCyclesHasQuotient` (definitions bundle `Q223SES005` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.PlaneCech.toric_H0_finite_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/KernelH1.lean (declaration OAI.MaximalSeshadri.PlaneCech.kernel_H1_finite)

import Mathlib
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K : Type*} [Field K] {ι : Type*}

variable [Fintype ι]

attribute [local instance] OAI.MaximalSeshadri.PlaneCech.kernelCyclesAddCommGroup
attribute [local instance] OAI.MaximalSeshadri.PlaneCech.kernelCyclesModule
attribute [local instance] OAI.MaximalSeshadri.PlaneCech.kernelCyclesHasQuotient
theorem kernel_H1_finite_s01 (N : Submodule (LaurentPlane.Ring K) (ι → LaurentPlane.Ring K)) (d : ℤ) :
    Module.Finite K ((cycles (K := K) (kernelA N) (kernelB N) (kernelC N d)) ⧸
      fullBoundaries (K := K) (kernelA N) (kernelB N) (kernelC N d)) := by
  sorry
end
end MaximalSeshadri.PlaneCech

end

end OAI
end
