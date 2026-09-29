-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines
-- name    : MvPolynomial.CrossingQuotient.Resolution.comap_iota_vanishingIdeal_closure_lines
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/0f4d80a9-daee-5e6d-a852-29585552cf04
-- title:
--   Chart pullbacks of the component ideal sheaves on the resolution
-- statement:
--   Fix a commutative ring $W$, an element $t \in W$ such that the quotient $W/(t)$ is reduced, and a natural number $e$; write $A =$ `CrossingQuotient W t` for the ring $W[X_0,X_1]/(X_0X_1 - t)$ and let `Resolution.ι t e j` denote, for $j : \mathrm{Fin}\,e$, the $j$-th chart morphism $\operatorname{Spec} A \to$ `Resolution t e`, where `Resolution t e` is the colimit of the gluing diagram `glueDiagram t e` indexed by `GlueIndex e`. Let $i : \mathrm{Fin}\,e$ and $k : \mathbb{N}$. Consider the closed subset of `Resolution t e` obtained as the closure of the union of the images under the chart maps of the zero loci of the elements `U t` and `V t` of $A$, namely of $\bigcup_{j : (j)+1 = k} \iota_j(Z(U\,t))$ together with $\bigcup_{j : (j) = k} \iota_j(Z(V\,t))$, and let its `vanishingIdeal` be the ideal sheaf data of the reduced induced structure on it. The assertion is that the pullback (`comap`) of this ideal sheaf data along the chart $\iota_i$ equals the ideal sheaf data `ofIdealTop` attached to the ideal of global sections of $\operatorname{Spec} A$ obtained by transporting, along the inverse of `Scheme.ΓSpecIso`, the ideal $(V\,t)$ if $k = i$, the ideal $(U\,t)$ if $k = i+1$, and the unit ideal otherwise.
--
--   This is the chart-by-chart table for the components of the special fibre of the explicit (toric) resolution of $uv = t^{e}$: on the $i$-th chart the component indexed by $k$ cuts out $(V\,t)$, $(U\,t)$ or nothing at all, so that the $C_k$ are the strict transforms of $u=0$, $v=0$ together with the $e-1$ exceptional lines. It feeds the assembly of the full chart table [`MvPolynomial.CrossingQuotient.Resolution.exists_idealSheafData_chartTable`](thm.html#MvPolynomial.CrossingQuotient.Resolution.exists_idealSheafData_chartTable) and, through it, the statements about components, intersections and reducedness used for the semistable models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_comap_iota_vanishingIdeal_closure_lines.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.comap_iota_vanishingIdeal_closure_lines
    {W : Type u} [CommRing W] (t : W) (e : ℕ) [IsReduced (W ⧸ Ideal.span {t})] (i : Fin e) (k : ℕ) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure
        ((⋃ (j : Fin e) (_ : (j : ℕ) + 1 = k), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {U t})) ∪
         (⋃ (j : Fin e) (_ : (j : ℕ) = k), (Resolution.ι t e j) '' (PrimeSpectrum.zeroLocus {V t}))),
        isClosed_closure⟩).comap (Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient W t))).inv.hom
        (if k = (i : ℕ) then Ideal.span {V t} else if k = (i : ℕ) + 1 then Ideal.span {U t} else ⊤)) := by sorry
