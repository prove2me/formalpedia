-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_quartic_integral
-- name    : OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:23.992551+00:00
-- url     : https://prove2.me/theorems/b42d5bb5-56e7-4a1c-a070-507422c65c4a
-- title:
--   Integral quartic sections of an ample power
-- statement:
--   For $L$ ample on $S$ there are $d>0$, $N,n$, sections $s$ of $L^d$ indexed by $\operatorname{Option}(\operatorname{Fin}N)$ with iso-opens covering $S$, an equivalence $e$ from $\operatorname{Option}(\operatorname{Fin}n)$ to `QuarticIndex (Fin N)`, and a point $y$ such that $y$ is the only point outside `centeredOpen s`, the sections define a closed immersion, and for every nonzero polynomial $P$ there is $v$ with $P(v)\ne0$ such that `doublePointQuarticIdeal k s hs (v ∘ e.symm)` has integral subscheme, smooth over $\mathbb C$ on the centered open.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. `centeredOpen s` is the union of the iso-opens of $s_{\mathrm{some}\,i}$. `QuarticIndex σ` is $\sigma\times\sigma\times\operatorname{Option}\sigma\times\operatorname{Option}\sigma$; `doublePointQuartics` are the corresponding degree-4 mixed products of the sections.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.ample_quartic_integral`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/GlobalIntegralQuartic.lean#L68

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section

section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Hartogs
open MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.ample_quartic_integral (S : Surface)
    (L : LineBundle S.scheme) (hL : LineBundle.IsAmple S.scheme L) :
    ∃ d : ℕ, 0 < d ∧ ∃ N n : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (modulePow S.scheme L.sheaf d),
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ e : Option (Fin n) ≃ QuarticIndex (Fin N), ∃ y : S.scheme,
        (∀ x : S.scheme, x ∉ centeredOpen s ↔ x = y) ∧
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) s hs) ∧
        ∀ P : MvPolynomial (Option (Fin n)) ℂ, P ≠ 0 →
          ∃ v : Option (Fin n) → ℂ, MvPolynomial.aeval v P ≠ 0 ∧
            let k := S.structureMap.appTop.hom.comp
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
            let V := centeredOpen s
            let J := doublePointQuarticIdeal k s hs (v ∘ e.symm)
            IsIntegral J.subscheme ∧
              Smooth ((J.comap V.ι).subschemeι ≫ V.ι ≫ S.structureMap) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
