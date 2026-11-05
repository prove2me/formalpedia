-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_exceptional_twist_sections_bounds
-- name    : OAI.MaximalSeshadri.Geometry.Surface.exceptional_twist_sections_bounds
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:05:15.024053+00:00
-- url     : https://prove2.me/theorems/67d4f60e-9ac3-4489-9008-431add5758f5
-- title:
--   Section counts on the blow-up of a surface
-- statement:
--   Let $S,T$ be surfaces with $L$ ample on $S$ and $A$ ample on $T$, $p$ a configuration of $r$ points on $S$, $f:T\to S$ a blow-up of the centre ideal over $\mathbb C$, and $J,\iota$ presenting the pullback of the ideal. Then for a line bundle $M$ on $S$ and $n\in\mathbb N$, $h^0(T,J^n\otimes f^*M)\le h^0(S,M)$ and $2h^0(S,M)\le 2h^0(T,J^n\otimes f^*M)+rn(n+1)$.
--
--   **Notation.** $h^n$ is `cohomologyDimension`, the `Module.finrank` over $\mathbb C$ of $\operatorname{Ext}^n(\mathcal O,-)$, which is 0 for an infinite-dimensional space. `PresentsPullbackIdeal I f J ι` says that $\iota:J\to\mathcal O_Y$ is a monomorphism whose image on affine opens is the extension of $I$ along $f$. `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property. `IsAmple` means that for each point $x$ and open $V\ni x$, some positive power has a global section with nonvanishing open containing $x$, inside $V$, and affine. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.exceptional_twist_sections_bounds`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupSectionDimensions.lean#L43

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

theorem Surface.exceptional_twist_sections_bounds (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    (A : LineBundle T.scheme) (hA : A.IsAmple)
    {r : ℕ} (p : Configuration S r) (f : T.scheme ⟶ S.scheme)
    (hf : f ≫ S.structureMap = T.structureMap)
    (hbl : IsBlowup (centreIdeal S r p) f)
    (J : LineBundle T.scheme) (ι : J.sheaf ⟶ O T.scheme)
    (hJ : PresentsPullbackIdeal (centreIdeal S r p) f J ι)
    (M : LineBundle S.scheme) (n : ℕ) :
    cohomologyDimension T.structureMap ((J.pow n).tensor (M.pullback f)).sheaf 0 ≤
      cohomologyDimension S.structureMap M.sheaf 0 ∧
    2*cohomologyDimension S.structureMap M.sheaf 0 ≤
      2*cohomologyDimension T.structureMap ((J.pow n).tensor (M.pullback f)).sheaf 0 + r*n*(n+1) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
