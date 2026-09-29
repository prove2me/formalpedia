-- Prove2me | Theorems.Thm_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom
-- name    : ModularCurve.mem_of_coeffMap_mem_adjoin_image_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ff64ad43-fd92-5aff-8085-4851268627c5
-- title:
--   Membership in F ≤ K((q)) descends along coefficientwise embeddings
-- statement:
--   Let $K$ and $L$ be fields and let $\iota : K \to L$ be a ring homomorphism. Write [`ModularCurve.coeffMap`](def/ModularCurve_LaurentCoeff.html#L16) $\iota$ for the induced ring homomorphism from the Laurent series field $K((q))$ to $L((q))$ obtained by applying $\iota$ to each coefficient of a Laurent (Hahn) series. Let $F$ be an intermediate field of the extension $K \subseteq K((q))$, that is, a subfield of $K((q))$ containing the constants $K$, and let $x \in K((q))$. Assume that the coefficientwise image of $x$ lies in the intermediate field of $L \subseteq L((q))$ generated over $L$ by the image set $(\mathrm{coeffMap}\ \iota)(F) \subseteq L((q))$, i.e. in $\mathrm{adjoin}_L$ of that image. The conclusion is that $x$ already belongs to $F$. Thus membership in $F$ can be tested after extending the field of constants from $K$ to $L$ along $\iota$: no element of $K((q))$ outside $F$ acquires an expression over $L$ in terms of the $\iota$-images of elements of $F$. No further hypothesis is placed on $\iota$ beyond being a homomorphism of fields.
--
--   This is the linear disjointness of the constant extension $L$ and $K((q))$ over $K$ inside $L((q))$, stated as a descent criterion for membership in a $q$-expansion field. It is used in the construction of two-chart integral models of modular curves, where a $q$-series with coefficients in $K$ is recognised as lying in a function field over $K$ after passing to a larger constant field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_of_coeffMap_mem_adjoin_image_of_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.mem_of_coeffMap_mem_adjoin_image_of_ringHom
    {K L : Type*} [Field K] [Field L] (ι : K →+* L) (F : IntermediateField K (LaurentSeries K))
    (x : LaurentSeries K)
    (hx : ModularCurve.coeffMap ι x ∈
      IntermediateField.adjoin L (ModularCurve.coeffMap ι '' (F : Set (LaurentSeries K)))) :
    x ∈ F := by sorry
