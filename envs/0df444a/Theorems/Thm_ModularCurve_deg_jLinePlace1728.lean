-- Prove2me | Theorems.Thm_ModularCurve_deg_jLinePlace1728
-- name    : ModularCurve.deg_jLinePlace1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/60ae1463-3d99-596c-bf72-18deed415732
-- title:
--   The j-line place at j=1728 has degree 1
-- statement:
--   Let `jq` be the transcendental element over $\mathbb{Q}$ out of which the $j$-line is built, and let $\mathbb{Q}\langle$`jq`$\rangle$ denote the intermediate field it generates; `jLineRingEquiv` is the ring isomorphism $\mathrm{RatFunc}\,\mathbb{Q} \cong \mathbb{Q}\langle$`jq`$\rangle$ sending the indeterminate to `jq`, obtained from the transcendence of `jq`. Here a place of an extension $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not the whole of $F$, and is a principal ideal ring, and its degree is the $K$-dimension of the residue field of that valuation subring. The place `jLinePlace1728` is the transport along `jLineRingEquiv` (which fixes $\mathbb{Q}$, so that the transported valuation subring, the preimage under the inverse isomorphism, is again a place over $\mathbb{Q}$) of the finite place `placeOfPoint ℚ 1728` of $\mathrm{RatFunc}\,\mathbb{Q}$ attached to the irreducible polynomial $X - 1728$. The theorem asserts that the degree of `jLinePlace1728` equals $1$; equivalently, its residue field is $\mathbb{Q}$ itself, so the place is rational.
--
--   This records that the point $j = 1728$ of the $j$-line is a rational place, one of the two distinguished points (together with $j = 0$, and the cusp) around which ramification of the modular covers is concentrated. It is used in the identification of the number of points of the modular curve with $\bar{j} = 1728$, respectively $\bar{j} = 0$, with the counts $\nu_2$ and $\nu_3$ of elliptic points of order $2$ and $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_deg_jLinePlace1728.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.deg_jLinePlace1728 : ModularCurve.jLinePlace1728.deg = 1 := by sorry
