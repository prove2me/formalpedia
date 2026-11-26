-- Prove2me | Theorems.Thm_HurewiczSketchV2_exists_hurewicz_hom
-- name    : HurewiczSketchV2.exists_hurewicz_hom
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-26T10:01:54.764151+00:00
-- url     : https://prove2.me/theorems/30f36e43-c8d2-4d54-9384-f08e30824eab
-- title:
--   Existence of the canonical Hurewicz homomorphism in degree n+2
-- statement:
--   Existence of the Hurewicz homomorphism in degree $r=n+2$.
--
--   For $r\ge 2$ and a pointed space $(Y,y)$ there is a canonical additive group homomorphism
--
--   $$h:\ \pi_r(Y,y)\ \longrightarrow\ H_r(Y;\mathbb{Z}),$$
--
--   the Hurewicz map.  A class in $\pi_r(Y,y)$ is represented by a based map $S^r\to Y$; pushing the fundamental singular cycle of $S^r$ forward gives a singular $r$-cycle in $Y$, and its homology class is $h$ of the original class.  Because $r\ge 2$, $\pi_r(Y,y)$ is abelian, so this is an additive homomorphism.
--
--   This child records only the existence of the canonical map.  Its bijectivity under the reduced-CW hypotheses is split into the two companion children (surjectivity from $r$-cells, injectivity from $(r+1)$-cells), so that no step is smuggled into this one.
--
--   **Formalization Note** The map is an `Additive (HomotopyGroup.Pi (n+2) Y y) →+ SP4Homology.H (n+2) Y`; the `Additive` wrapper turns the (abelian) homotopy group into an additive group, and `→+` is an additive homomorphism.  The target `SP4Homology.H` is Mathlib's integral singular homology object.
-- source:
--   A. Hatcher, Algebraic Topology, Cambridge University Press (2002), §4.2 Theorem 4.32 (Hurewicz) p. 366 and Proposition 4.13 (cellular approximation) p. 353; and https://zhuanlan.zhihu.com/p/2063085365225863035 (the three-step proof sketch followed here).

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Category.TopCat.Basic
import Definitions.Def_HurewiczSketchV2
import Definitions.Def_SP4Homology

set_option autoImplicit false

namespace HurewiczSketchV2

/-- Existence of the Hurewicz homomorphism in degree `r = n+2`.

For `r ≥ 2` and any pointed space `(Y,y)`, there is a canonical additive homomorphism
`h : π_r(Y,y) → H_r(Y;ℤ)`, the Hurewicz map.  On a based map `S^r → Y` representing
an element of `π_r`, it takes the homology class of the corresponding singular cycle;
it is a group homomorphism because `π_r` is abelian for `r ≥ 2`.  This child records only
the existence of this canonical additive map; bijectivity under the reduced-CW hypotheses
is the content of the two companion children. -/
theorem exists_hurewicz_hom (n : ℕ) (Y : TopCat) (y : Y) :
    Nonempty (Additive (HomotopyGroup.Pi (n + 2) Y y) →+ SP4Homology.H (n + 2) Y) := by
  sorry

end HurewiczSketchV2
