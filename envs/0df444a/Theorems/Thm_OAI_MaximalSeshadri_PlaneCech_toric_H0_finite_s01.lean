-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_PlaneCech_toric_H0_finite_s01
-- name    : OAI.MaximalSeshadri.PlaneCech.toric_H0_finite_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:17:00.132486+00:00
-- url     : https://prove2.me/theorems/6ceda339-8616-4759-899a-12db9add5db6
-- title:
--   OAI.MaximalSeshadri.PlaneCech.toric_H0_finite_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.PlaneCech.toric_H0_finite` of [lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ToricH0.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ToricH0.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.PlaneCech`, with `open LaurentPlane`):
--
--   ```lean
--   theorem toric_H0_finite_s01 (V : Fin 3 → Submodule K M)
--       (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
--       {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
--       (hg : ∀ i a, g i a ∈ V i)
--       (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
--       (clear : ∀ i j (x : M), x ∈ V j →
--         ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
--       Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.LaurentPlane.Ring`, `OAI.MaximalSeshadri.LaurentPlane.T`, `OAI.MaximalSeshadri.PlaneCech.vertexCone` and `OAI.MaximalSeshadri.PlaneCech.weight` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.PlaneCech.monomialSpan` (definitions bundle `Q223SES005` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.finite_projection_H0_finite_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Cohomology/ToricH0.lean (declaration OAI.MaximalSeshadri.PlaneCech.toric_H0_finite)

import Mathlib
import Definitions.Def_Q223SES005

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]

theorem toric_H0_finite_s01 (V : Fin 3 → Submodule K M)
    (stable : ∀ i z, z ∈ vertexCone i → ∀ x ∈ V i, T (K := K) z • x ∈ V i)
    {ι : Fin 3 → Type*} [∀ i, Fintype (ι i)] (g : ∀ i, ι i → M)
    (hg : ∀ i a, g i a ∈ V i)
    (hgen : ∀ i, V i = monomialSpan (K := K) (vertexCone i) (g i))
    (clear : ∀ i j (x : M), x ∈ V j →
      ∃ d : ℕ, T (K := K) (d • (weight j-weight i)) • x ∈ V i) :
    Module.Finite K ↥((V 0 ⊓ V 1) ⊓ V 2) := by
  sorry
end
end MaximalSeshadri.PlaneCech

end

end OAI
end
