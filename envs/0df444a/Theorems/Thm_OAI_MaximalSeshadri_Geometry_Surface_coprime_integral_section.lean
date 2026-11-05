-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section
-- name    : OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:32.576308+00:00
-- url     : https://prove2.me/theorems/cfb19a04-93b2-43a4-8323-344084dddc93
-- title:
--   Sections of coprime degree with integral zero loci
-- statement:
--   Let $L$ be ample on a surface $S$ and $a>0$. There are $b>0$ coprime to $a$, a finite family $s$ of sections of $L^b$ with iso-opens covering $S$, and coefficients $v\in\mathbb C$, such that the combination is nonzero and its section ideal defines an integral subscheme of dimension one.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.coprime_integral_section`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Divisors/CoprimeDivisor.lean#L21

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral
attribute [local instance] MvPolynomial.gradedAlgebra

theorem Surface.coprime_integral_section (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ ∃ N : ℕ,
      ∃ s : Option (Fin N) → GlobalSections S.scheme (L.pow b).sheaf,
      ∃ hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤,
      ∃ v : Option (Fin N) → ℂ,
        let k := S.structureMap.appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        sectionCombination k s v ≠ 0 ∧ IsIntegral (sectionIdeal k s hs v).subscheme ∧
          topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1 := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
