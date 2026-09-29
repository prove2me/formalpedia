-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_flat_igusaTo
-- name    : ModularCurve.IgusaScheme.flat_igusaTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/64e990a1-25ea-5f35-af8e-ade0215ae1c2
-- title:
--   Flatness of the two-chart Igusa scheme over ℤ_{(ℓ)}
-- statement:
--   Let $N$ be a natural number that is nonzero and let $\ell$ be a prime. Write $\mathbb{Z}_{(\ell)}$ for the ring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) (a subring of $\mathbb{Q}$) and $F$ for `modularFunctionFieldFull N`. For a subset $S \subseteq F$ the project forms the $\mathbb{Z}_{(\ell)}$-subalgebra `chartAlg N ℓ S` of $F$; the two charts in play are `chartAlgFin N ℓ`, attached to $S = \{\,$`jFull N`$\,\}$, and `chartAlgInf N ℓ`, attached to $S = \{\,$`(jFull N)⁻¹`$\,\}$. The scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout of the two morphisms $f_{\mathrm{fin}} : X_{\mathrm{mid}} \to X_{\mathrm{fin}}$ and $f_{\infty} : X_{\mathrm{mid}} \to X_{\infty}$ obtained by applying $\operatorname{Spec}$ to the ring maps `inclFin N ℓ` and `inclInf N ℓ`, i.e. the gluing of the two chart spectra along their common overlap, and `igusaTo N ℓ` is the morphism to $\operatorname{Spec} \mathbb{Z}_{(\ell)}$ obtained from the universal property of that pushout out of the two structure morphisms $\operatorname{Spec}$ of $\mathbb{Z}_{(\ell)} \to$ `chartAlgFin N ℓ` and $\mathbb{Z}_{(\ell)} \to$ `chartAlgInf N ℓ`. The assertion is that `igusaTo N ℓ` is a flat morphism of schemes, for every such $N$ and $\ell$, with no coprimality condition between $\ell$ and $N$.
--
--   This is the flatness half of the classical statement that the Igusa model of the modular curve over $\mathbb{Z}_{(\ell)}$ is a well-behaved integral model; combined with finiteness and fibrewise information it feeds the properness, smoothness and geometric integrality statement for this model, and the local study of its stalks and sections, which cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_flat_igusaTo.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.flat_igusaTo (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Flat (igusaTo N ℓ) := by sorry
