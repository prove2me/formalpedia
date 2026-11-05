-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_projective_nodal_degree_bound
-- name    : OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:06:42.980533+00:00
-- url     : https://prove2.me/theorems/b82d8600-fb7b-4bbe-b1d5-4a60b4d25ee5
-- title:
--   Branch orders at a node are bounded by the degree
-- statement:
--   On a projective curve $X$ over $\mathbb C$, let $s\ne0$ be a section of a line bundle $L$, with an open immersion $i:Y\to X$ from a nonempty affine Noetherian scheme and a trivialization on $Y$. Let $R$ be a domain over $\mathbb C$ of dimension at most 2 with a surjection $\pi:R\to\Gamma(Y)$ with kernel the prime $(g)$, and $q$ an analytic family of points of $R$ with exact jets with $q_z(g)=u(z)z_1z_2$ near 0, $u(0)\ne0$. If $f\notin(g)$ maps to the coefficient of $s$, then the sum of orders of the restrictions of the Taylor expansion of $f$ to the two axes is at most $\chi(L)-\chi(\mathcal O_X)$.
--
--   **Notation.** $\chi$ is `eulerCharacteristic`: the alternating sum of $\mathbb C$-dimensions of $\operatorname{Ext}^n(\mathcal O,-)$, for $n\le2$ on a surface and $n\le1$ on a curve. The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$. The Taylor maps (`analyticTaylor`, `bivariateTaylor`) send a function to the power series of $z\mapsto q_z(\cdot)$ at $0$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.projective_nodal_degree_bound`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalCurveDegree.lean#L25

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.LocalComparison MaximalSeshadri.NodalLocal
open scoped Topology

variable {X Y : Scheme.{0}}

theorem projective_nodal_degree_bound [IsIntegral X] [IsNoetherian X]
    {σ : Type} [Fintype σ]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (a : σ → (O X ⟶ M)) (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
    (L : LineBundle X) (s : O X ⟶ L.sheaf) (hs : s ≠ 0)
    (i : Y ⟶ X) [IsOpenImmersion i] [IsAffine Y] [IsNoetherian Y] [Nonempty Y]
    (e : L.sheaf.restrict i ≅ O Y)
    {R : Type} [CommRing R] [Algebra ℂ R] [IsDomain R]
    (hR : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ t, AnalyticAt ℂ (fun z => q z t) 0)
    (hjets : ∀ n : ℕ,
      RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
          (RingHom.ker (q 0))^n ∧
      Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom))
    (f g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) (hf : f ∉ Ideal.span {g})
    (π : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
      R →ₐ[ℂ] Γ(Y,⊤)) (hπ : Function.Surjective π)
    (hker : letI : Algebra ℂ Γ(Y,⊤) := (baseScalars (i ≫ p)).toAlgebra
      RingHom.ker π.toRingHom = Ideal.span {g})
    (hcoeff : π f = coefficient e (restrictSection i s)) :
    (((restrictX ℂ (bivariateTaylor q hq f)).order.toNat +
      (restrictZ ℂ (bivariateTaylor q hq f)).order.toNat : ℕ) : ℤ) ≤
        eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
