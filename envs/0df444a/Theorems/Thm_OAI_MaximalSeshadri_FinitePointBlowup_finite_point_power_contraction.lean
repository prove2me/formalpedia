-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_FinitePointBlowup_finite_point_power_contraction
-- name    : OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:58.187194+00:00
-- url     : https://prove2.me/theorems/c876e5a4-dcc7-49e8-b2fb-639a8e2678e8
-- title:
--   Contraction of ideal powers on a blow-up of finitely many points
-- statement:
--   Let $K$ be a field, $X$ smooth of relative dimension 2 over $\operatorname{Spec}K$, $p_i$ finitely many sections of $X\to\operatorname{Spec}K$ with distinct images, and $\pi:B\to X$ a blow-up of the product $\mathcal I=\prod_i\ker p_i$. For every $m$, the image ideal of $(\pi^{-1}\mathcal I)^m$ under $\pi$ is $\mathcal I^m$; that is, `((pointCentre p).comap π)^m` maps to `(pointCentre p)^m`.
--
--   **Notation.** `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.FinitePointBlowup.finite_point_power_contraction`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/FiniteCenters.lean#L262

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

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

include hp

variable (hd : Function.Injective (fun i =>
  p i (⟨⊥, Ideal.isPrime_bot⟩ : Spec (.of K))))

include hd

end
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

theorem finite_point_power_contraction [SmoothOfRelativeDimension 2 f]
    (π : B ⟶ X) (hπ : IsBlowup (pointCentre p) π) (m : ℕ) :
    (((pointCentre p).comap π)^m).map π = (pointCentre p)^m := by
  sorry

end
end MaximalSeshadri.FinitePointBlowup
end
end OAI
