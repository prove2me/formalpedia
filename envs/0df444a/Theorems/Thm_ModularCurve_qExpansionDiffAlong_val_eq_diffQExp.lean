-- Prove2me | Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
-- name    : ModularCurve.qExpansionDiffAlong_val_eq_diffQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8c6f8c59-9a59-568f-8c29-ce9bf3b58bce
-- title:
--   q-expansion differential along an inclusion agrees with `diffQExp`
-- statement:
--   Let $L$ be a field and let $F$ be an intermediate field of the formal Laurent series field $L((q))$ over $L$, i.e. a subfield of `LaurentSeries L` containing the image of $L$. Let $\omega$ be an element of the module $\Omega[F\,/\,L]$ of Kähler differentials of $F$ over $L$. Two maps into $L((q))$ are compared. The first is `qExpansionDiffAlong` applied to the inclusion $F \to L((q))$ (the algebra map `F.val`): by definition this is, whenever such a map exists, a chosen $L$-linear map $\varphi : \Omega[F\,/\,L] \to L((q))$ satisfying $\varphi(D_{L}x) = \mathrm{thetaL}(x)$ for every $x \in F$, where `thetaL` is the operator $q\,d/dq$ on Laurent series, and $\varphi(f \cdot \omega) = f\,\varphi(\omega)$ for $f \in F$ and $\omega \in \Omega[F\,/\,L]$, and is the zero map when no such $\varphi$ exists. The second is `diffQExp F`, the $F$-linear map obtained from the universal property of Kähler differentials applied to the derivation $L \to F \to L((q))$ got by restricting `qEuler L` along the inclusion of $F$. The assertion is that the two maps take the same value at $\omega$; since $\omega$ is arbitrary, the choice implicit in `qExpansionDiffAlong` is thereby pinned down.
--
--   This is the generic form of the identification of the abstractly characterised $q$-expansion differential operator along an embedding with the concrete Euler derivation lift $q\,d/dq$ on a subfield of $L((q))$. It is used, at $L$ an algebraic closure of $\mathbb{Q}$ and $F$ a modular function field, in the statements computing $q$-expansions of differentials on modular curves and in the Frobenius-compatibility statements for Hecke operators that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExp {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    qExpansionDiffAlong F.val ω = diffQExp F ω := by sorry
