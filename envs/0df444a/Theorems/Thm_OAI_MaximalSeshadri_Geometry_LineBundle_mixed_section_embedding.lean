-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_LineBundle_mixed_section_embedding
-- name    : OAI.MaximalSeshadri.Geometry.LineBundle.mixed_section_embedding
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:17:36.417193+00:00
-- url     : https://prove2.me/theorems/a8cc9349-c488-4fd8-8840-1d73d54cfd63
-- title:
--   Embedding by mixed sections
-- statement:
--   Let $X$ be integral and compact, proper over a commutative ring $K$, $L,M$ line bundles, $s_i$ a finite family of sections of $L$ with nonvanishing opens affine, nonempty and covering $X$, and trivializations of $M$ on those opens. Then there are $n>0$ and finitely many sections of $L^n\otimes M$ with iso-opens covering $X$ defining a closed immersion to $\operatorname{Proj}$ over $K$.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionOpen X s` is the same union for a global section $s$: its nonvanishing open. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.LineBundle.mixed_section_embedding`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/MixedEmbedding.lean#L19

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.TensorPure MaximalSeshadri.Projective

variable {X : Scheme.{0}} {K ι : Type} [CommRing K] [Fintype ι]

theorem LineBundle.mixed_section_embedding [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] (L M : LineBundle X)
    (s : ι → GlobalSections X L.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (sectionOpen X (s i)))
    (hne : ∀ i, (sectionOpen X (s i) : Set X).Nonempty)
    (d : ∀ i, M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X ((L.pow n).tensor M).sheaf,
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
