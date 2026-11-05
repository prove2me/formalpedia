-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_ample_embedding
-- name    : OAI.MaximalSeshadri.Geometry.Surface.ample_embedding
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:10:04.326942+00:00
-- url     : https://prove2.me/theorems/15ee78b7-2317-404e-9fb7-8dc0ddfa4e0e
-- title:
--   Sections of an ample power embed a surface
-- statement:
--   For $L$ ample on a surface $S$ there are $n>0$ and a finite family of sections of $L^n$ with iso-opens covering $S$ such that `sectionsMorphism` over $\mathbb C$ is a closed immersion.
--
--   **Notation.** The iso-open of $s$ (`SectionOpens.isoOpen s`) is the union of the opens on which the morphism $s$ restricts to an isomorphism. `sectionsMorphism k s hs` is the morphism from $X$ to $\operatorname{Proj}$ of the graded polynomial ring in variables indexed by the sections, defined by sections whose iso-opens cover $X$, with $k$ the ring map from the base into $\Gamma(X,\top)$. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.ample_embedding`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Projective/AmpleEmbedding.lean#L110

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Projective

theorem Surface.ample_embedding (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections S.scheme (modulePow S.scheme L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) t ht) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end
end
end OAI
