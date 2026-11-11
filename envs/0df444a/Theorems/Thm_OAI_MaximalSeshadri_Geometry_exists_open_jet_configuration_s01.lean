-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_exists_open_jet_configuration_s01
-- name    : OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:14:31.954634+00:00
-- url     : https://prove2.me/theorems/aab5d3a8-a52b-4285-be35-c7c5d2f899b0
-- title:
--   OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration` of [lean/OAI/AlgebraicGeometry/Seshadri/Jets/JetOpenConfigurations.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/JetOpenConfigurations.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.Geometry`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.ProjectiveBertini`):
--
--   ```lean
--   theorem exists_open_jet_configuration_s01 (S : Surface) (r : ℕ)
--       (U : S.scheme.affineOpens) (t : Fin 2 → Γ(S.scheme,U.1))
--       (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
--       {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
--       (ℓ : letI := (openScalars S.structureMap U.1).toAlgebra;
--         A →ₗ[ℂ] Γ(S.scheme,U.1))
--       (m : ℕ) (hm : 0 < m)
--       (p : letI := (openScalars S.structureMap U.1).toAlgebra;
--         Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
--       (hp : ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (p i))^m) → a = 0) :
--       ∃ W : (surfacePower S r).left.Opens,
--         tupleImage S r (fun i => affineComplexPoint S.structureMap U (p i)) ∈ W ∧
--         ∀ q : Fin r → ComplexPoint S, tupleImage S r q ∈ W →
--           ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
--             Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
--             (∀ i, affineComplexPoint S.structureMap U (ρ i) = q i) ∧
--             ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (ρ i))^m) → a = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.Geometry.affineComplexPoint` and `OAI.MaximalSeshadri.ProjectiveBertini.openScalars` (definitions bundle `Q223SES002` of this split); `OAI.MaximalSeshadri.Geometry.ComplexPoint`, `OAI.MaximalSeshadri.Geometry.Surface`, `OAI.MaximalSeshadri.Geometry.complexBase`, `OAI.MaximalSeshadri.Geometry.surfacePower` and `OAI.MaximalSeshadri.Geometry.tupleImage` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/JetOpenConfigurations.lean (declaration OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES002

section

attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

theorem exists_open_jet_configuration_s01 (S : Surface) (r : ℕ)
    (U : S.scheme.affineOpens) (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ℓ : letI := (openScalars S.structureMap U.1).toAlgebra;
      A →ₗ[ℂ] Γ(S.scheme,U.1))
    (m : ℕ) (hm : 0 < m)
    (p : letI := (openScalars S.structureMap U.1).toAlgebra;
      Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hp : ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (p i))^m) → a = 0) :
    ∃ W : (surfacePower S r).left.Opens,
      tupleImage S r (fun i => affineComplexPoint S.structureMap U (p i)) ∈ W ∧
      ∀ q : Fin r → ComplexPoint S, tupleImage S r q ∈ W →
        ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
          (∀ i, affineComplexPoint S.structureMap U (ρ i) = q i) ∧
          ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (ρ i))^m) → a = 0 := by
  sorry
end
end MaximalSeshadri.Geometry

end

end OAI
end
