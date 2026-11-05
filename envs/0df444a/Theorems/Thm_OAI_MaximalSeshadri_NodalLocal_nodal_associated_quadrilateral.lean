-- Prove2me | Theorems.Thm_OAI_MaximalSeshadri_NodalLocal_nodal_associated_quadrilateral
-- name    : OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T15:17:56.0864+00:00
-- url     : https://prove2.me/theorems/8c17ec55-c2bb-4285-8b0b-5f420cd1b9c6
-- title:
--   Initial exponents at a node lie in a quadrilateral
-- statement:
--   In $\mathbb C[[x,z]]$, let $u$ be a unit, $f$ with nonzero restrictions to both axes, and $g$ associated to $(u\cdot xz)^jf$. Let $d,H,t,k>0$ and $n$ with $\dim\mathbb C[[x,z]]/(f,xz)\le ndH$ and $n+jd=k$. If $p$ is the lexicographic initial exponent of $g$ for weight $t$, then $p$ lies in `nodeQuadrilateral` with vertices $(0,0)$, $(kdHt/(1+t),0)$, $(k/d,k/d)$, $(0,kdH/(1+t))$.
--
--   **Notation.** `sectionIdeal k s hs v` is the comap along `sectionsMorphism` of the ideal sheaf of the hyperplane with coefficients $v$; `sectionCombination k s v` is $\sum_j k(v_j)s_j$. `nodeQuadrilateral a b c` is the convex hull of $(0,0),(a,0),(c,c),(0,b)$. `LexInitial c t e` says that $c_e\ne0$ and $e$ minimizes $p_1+tp_2$ among exponents with nonzero coefficient, ties broken by the smaller second coordinate.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with `Definitions` files of this development imported in place of the upstream modules; these are supporting code for the statement.
-- source:
--   OpenAI, Maximal Seshadri constants on arbitrary polarized surfaces, September 23, 2026, https://github.com/openai/math (paper: preprints/Maximal-Seshadri-Constants-on-Arbitrary-Polarized-Surfaces-September-23-2026/main.pdf; Lean: lean/OAI/AlgebraicGeometry/Seshadri, Apache License 2.0); Lean declaration `OAI.MaximalSeshadri.NodalLocal.nodal_associated_quadrilateral`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/AlgebraicGeometry/Seshadri/Nodal/NodalAssociated.lean#L29

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6

namespace OAI

section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open PowerSeries

theorem nodal_associated_quadrilateral (u f g : Bivariate ℂ) (j : ℕ)
    (d H t k n : ℝ) (hd : 0 < d) (hH : 0 < H) (ht : 0 < t) (hk : 0 < k)
    (hu : IsUnit u) (hx : restrictX ℂ f ≠ 0) (hz : restrictZ ℂ f ≠ 0)
    (hcolength : (Module.finrank ℂ (Bivariate ℂ ⧸ intersectionIdeal ℂ f) : ℝ) ≤ n*d*H)
    (hdegree : n+(j:ℝ)*d=k) (hassoc : Associated ((u*nodeEquation ℂ)^j*f) g)
    (p : Exponent) (hp : LexInitial (bivariateCoeff g) t p) :
    ((p.1:ℝ),(p.2:ℝ)) ∈ nodeQuadrilateral
      (k*(d*H*t/(1+t))) (k*(d*H/(1+t))) (k/d) := by
  sorry

end
end MaximalSeshadri.NodalLocal
end
end OAI
