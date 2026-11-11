-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_FinitePointBlowup_finite_point_power_contraction_s01
-- name    : OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T14:49:03.348805+00:00
-- url     : https://prove2.me/theorems/651d6458-2d04-43ce-8d01-d90a23ab10ef
-- title:
--   OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction_s01: intermediate lemma from OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Maximal Seshadri constants on arbitrary polarized surfaces (result family 039)*, OpenAI Math Release, September 23, 2026, result family 39, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction` of [lean/OAI/AlgebraicGeometry/Seshadri/Blowup/FiniteCenters.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/FiniteCenters.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MaximalSeshadri.FinitePointBlowup`, with `open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace`, `open MaximalSeshadri.Geometry`):
--
--   ```lean
--   theorem finite_point_power_contraction_s01 [SmoothOfRelativeDimension 2 f]
--       (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (m : ℕ) :
--       (((pointCentre p).comap π)^m).map π = (pointCentre p)^m
--   ```
--
--   **Definitions.** The statement is written with `OAI.MaximalSeshadri.FinitePointBlowup.pointCentre` (definitions bundle `Q223SES001` of this split); `OAI.MaximalSeshadri.Geometry.IsBlowup` (the published bundle `Def_MaximalSeshadriConstants`).
--
--   **Used by.** The proof of `OAI.MaximalSeshadri.Geometry.PointBlowup.effective_twist_bound_s01` of this split imports it.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces (result family 039), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 39; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/FiniteCenters.lean (declaration OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction)

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES001

section

attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MaximalSeshadri.FinitePointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Geometry
variable {K : Type} [Field K] {X B : Scheme.{0}}
variable {α : Type} [Fintype α]
variable (p : α → (Spec (.of K) ⟶ X))
variable (f : X ⟶ Spec (.of K)) (hp : ∀ i, p i ≫ f = 𝟙 _)
variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hp hd

theorem finite_point_power_contraction_s01 [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (m : ℕ) :
    (((pointCentre p).comap π)^m).map π = (pointCentre p)^m := by
  sorry

end

end MaximalSeshadri.FinitePointBlowup

end

end OAI
end
