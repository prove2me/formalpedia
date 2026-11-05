-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_blowup_structureMap_isIso
-- name    : OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T15:04:51.908404+00:00
-- url     : https://prove2.me/theorems/bbd1d0c1-ee26-4444-bf01-bbe54bf9009f
-- title:
--   The blow-up of a configuration has trivial direct image of the structure sheaf
-- statement:
--   Let $S$ be a surface, $p$ a configuration of $r$ points, $B$ an integral scheme and $\pi:B\to S$ a quasi-compact blow-up of the centre ideal. Then $\mathcal O_S\to\pi_*\mathcal O_B$ is an isomorphism.
--
--   **Notation.** `IsBlowup I π` says that $I$ pulls back to an invertible ideal along $\pi$ and that $\pi$ is universal with this property. A `Surface` is an integral scheme smooth of relative dimension 2 over $\operatorname{Spec}\mathbb C$ with a closed immersion into some complex projective space over $\mathbb C$. `Configuration S r` is the set of $r$-tuples of complex points with distinct images, with the Zariski topology induced from the product.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.Geometry.Surface.blowup_structureMap_isIso`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Blowup/BlowupSectionDescent.lean#L69

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.blowup_structureMap_isIso (S : Surface) {r : ℕ} (p : Configuration S r)
    {B : Scheme.{0}} [IsIntegral B] {π : B ⟶ S.scheme} [QuasiCompact π]
    (hπ : IsBlowup (centreIdeal S r p) π) :
    IsIso (IdealModule.structureMap π) := by
  sorry

end
end MaximalSeshadri.Geometry
end
end OAI
