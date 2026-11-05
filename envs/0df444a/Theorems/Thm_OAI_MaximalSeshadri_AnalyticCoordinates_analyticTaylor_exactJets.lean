-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_AnalyticCoordinates_analyticTaylor_exactJets
-- name    : OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:07:11.758816+00:00
-- url     : https://prove2.me/theorems/df150f2a-0e51-43a9-8048-e0d54e78a25d
-- title:
--   The analytic Taylor map has exact jets
-- statement:
--   Let $S$ be a $\mathbb C$-algebra, formally étale and essentially of finite type over $\mathbb C[x_0,x_1]$. Let $q$ be a family of $\mathbb C$-points of $S$ parametrized by $\mathbb C^2$, analytic at 0, such that $z\mapsto(q_z(x_1),q_z(x_0))$ has an invertible derivative at 0. Then for all $n$ the composite of the Taylor map to $\mathbb C[[x,z]]$ with reduction modulo $\mathfrak m^n$ has kernel $(\ker q_0)^n$ and is surjective.
--
--   **Notation.** The Taylor maps (`analyticTaylor`, `bivariateTaylor`) send a function to the power series of $z\mapsto q_z(\cdot)$ at $0$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Jets/AnalyticFullRank.lean#L123

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology

open AlgebraicJets FormalCoordinates MvPolynomial
variable {S : Type*} [CommRing S] [Algebra ℂ S]

theorem analyticTaylor_exactJets
    [Algebra (MvPolynomial (Fin 2) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
    (he : HasFDerivAt (fun z =>
      (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
       q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))))
       (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
        (RingHom.ker (q 0))^n ∧
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) := by
  sorry

end
end MaximalSeshadri.AnalyticCoordinates
end
end
end
end OAI
