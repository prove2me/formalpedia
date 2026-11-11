-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_QuadraticJets_etale_ordinary_node_realization_s01
-- name    : OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:01:57.552475+00:00
-- url     : https://prove2.me/theorems/f3498032-519a-42f7-a5d2-2482b8c2d862
-- title:
--   OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization` of [lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNode.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNode.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.QuadraticJets`, with `open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticNode`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem etale_ordinary_node_realization_s01
--       (ρ : A →ₐ[ℂ] ℂ)
--       (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
--       (τ : A →ₐ[ℂ] JetAlgebra (Fin 2) ℂ 3)
--       (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
--       (hcoord : ∀ i, τ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
--         Ideal.Quotient.mk _ (X i))
--       (f : A) (hf : f ∈ (RingHom.ker ρ)^2) (hdisc : discriminant (τ f) ≠ 0) :
--       ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
--         (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
--         ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
--           (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
--           (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt
--             (fun z => (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
--               q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))))
--             (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
--           ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.AlgebraicJets.JetAlgebra` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.QuadraticJets.discriminant` (definitions bundle `Q223SES008` of this split).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNode.lean (declaration OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization)

import Mathlib
import Definitions.Def_Q223SES008

section

attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticNode
open scoped Topology ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem etale_ordinary_node_realization_s01
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (τ : A →ₐ[ℂ] JetAlgebra (Fin 2) ℂ 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
      Ideal.Quotient.mk _ (X i))
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) (hdisc : discriminant (τ f) ≠ 0) :
    ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
        (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt
          (fun z => (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
            q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))))
          (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
        ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  sorry
end
end MaximalSeshadri.QuadraticJets
end

end
end

end OAI
end
