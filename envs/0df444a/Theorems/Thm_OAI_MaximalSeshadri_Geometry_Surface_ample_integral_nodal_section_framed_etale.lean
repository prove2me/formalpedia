-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_integral_nodal_section_framed_etale
-- name    : OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:00.451487+00:00
-- url     : https://prove2.me/theorems/4bd910e6-cf4c-4a76-96a0-c1030d996655
-- title:
--   An integral nodal section of an ample power, framed on an étale chart
-- statement:
--   For $L$ ample on a surface $S$ there are $d>0$, sections $s_{\mathrm{none}},s_0,\dots,s_{N-1}$ of $L^d$ with iso-opens covering $S$, a point $y$, an affine open $U\ni y$ inside the iso-open of $s_{\mathrm{none}}$ on which $L$ is trivial, étale coordinates $t_1,t_2$ on $U$, and coefficients $v$ on the index type `QuarticIndex (Fin N)` with the following properties. The point $y$ is the unique point outside `centeredOpen s`. The ideal `doublePointQuarticIdeal k s hs v` defines an integral subscheme of dimension one, invertible on $S$, containing $y$, with nonzero defining section, and smooth over $\mathbb C$ on the centered open. Writing $f$ for its local equation on $U$, the ideal $(f)$ is prime, $f\neq0$, $\dim\Gamma(U)\le2$, and there is a family $q$ of $\mathbb C$-points of $\Gamma(U)$ parametrized by $\mathbb C^2$, with $\ker q_0$ the prime of $y$, $f(q_0)=0$, analytic at 0, injective on a neighbourhood of 0, with invertible derivative in two section ratios, with $q_z(f)=u(z)z_1z_2$ near 0 for an analytic $u$ with $u(0)\ne0$, and such that the Taylor map is injective and has exact $n$-jets with kernel the $n$-th power of the prime of $y$ for all $n$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionOpen X s` is the same union for a global section $s$: its nonvanishing open. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. The Taylor maps (`analyticTaylor`, `bivariateTaylor`) send a function to the power series of $z\mapsto q_z(\cdot)$ at $0$. `centeredOpen s` is the union of the iso-opens of $s_{\mathrm{some}\,i}$. `QuarticIndex σ` is $\sigma\times\sigma\times\operatorname{Option}\sigma\times\operatorname{Option}\sigma$; `doublePointQuartics` are the corresponding degree-4 mixed products of the sections.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.ample_integral_nodal_section_framed_etale`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/EtaleNodalDivisor.lean#L30

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
open MaximalSeshadri.AnalyticCoordinates
open scoped Topology

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_integral_nodal_section_framed_etale (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ y : S.scheme, ∃ U : S.scheme.affineOpens, ∃ hyU : y ∈ U.1,
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
      ∃ _ : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
        (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        let _ : Algebra ℂ Γ(S.scheme, U.1) := (openScalars S.structureMap U.1).toAlgebra
        ∃ v : QuarticIndex (Fin N) → ℂ,
          (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
          IsIntegral (doublePointQuarticIdeal k s hs v).subscheme ∧
          topologicalKrullDim (doublePointQuarticIdeal k s hs v).subscheme = 1 ∧
          InvertiblePullbackIdeal (doublePointQuarticIdeal k s hs v) (𝟙 S.scheme) ∧
          y ∈ (doublePointQuarticIdeal k s hs v).support ∧
          sectionCombination k (doublePointQuartics s) v ≠ 0 ∧
          Smooth (((doublePointQuarticIdeal k s hs v).comap (centeredOpen s).ι).subschemeι ≫
            (centeredOpen s).ι ≫ S.structureMap) ∧
          let f := U.1.topIso.hom (coefficient
            (sectionFrameOn (powerSection (s none) 4) U.1
              (hU.trans (sectionOpen_le_powerSection (s none) 4)))
            (restrictSection U.1.ι (sectionCombination k (doublePointQuartics s) v)))
          ∃ q : (ℂ × ℂ) → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
            ringKrullDim Γ(S.scheme,U.1) ≤ 2 ∧ (Ideal.span {f}).IsPrime ∧
            f ≠ 0 ∧ q 0 f = 0 ∧
            RingHom.ker (q 0) = (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal ∧
            ∃ hq : (∀ a, AnalyticAt ℂ (fun z => q z a) 0),
            ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
              (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
              (∃ i : Fin 2 → Fin N, ∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ),
                HasFDerivAt (fun z =>
                  (q z (-affineSectionRatios s U hU (some (i 1))),
                   q z (-affineSectionRatios s U hU (some (i 0)))))
                  (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
              (∀ n : ℕ, RingHom.ker ((Ideal.Quotient.mk
                (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                (analyticTaylor q hq).toRingHom) =
                  (U.2.isoSpec.hom ⟨y,hyU⟩).asIdeal^n ∧
                Function.Surjective ((Ideal.Quotient.mk
                  (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^n)).comp
                  (analyticTaylor q hq).toRingHom)) ∧
              Function.Injective (analyticTaylor q hq) ∧
              ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
