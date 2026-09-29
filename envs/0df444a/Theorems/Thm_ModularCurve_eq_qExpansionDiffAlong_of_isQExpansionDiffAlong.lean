-- Prove2me | Theorems.Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong
-- name    : ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/33b93a6a-dfeb-53ad-9a08-b92cbe4bc35e
-- title:
--   Uniqueness of the q-expansion differential map along σ
-- statement:
--   Let $K$, $F$ and $L$ be fields with $F$ and $L$ both $K$-algebras, and let $\sigma : F \to L((q))$ be a $K$-algebra homomorphism from $F$ into the field of formal Laurent series over $L$. Let $\varphi : \Omega_{F/K} \to L((q))$ be a $K$-linear map on the module of Kähler differentials, and suppose $\varphi$ satisfies the two conditions making up `IsQExpansionDiffAlong σ`: first, for every $x \in F$ one has $\varphi(\mathrm{d}_{K/F} x) = \theta(\sigma x)$, where $\theta$ is the $L$-linear operator $f \mapsto q \cdot f'$ on $L((q))$ given by multiplying the formal derivative by the monomial $q$ with coefficient $1$; second, $\varphi$ is $\sigma$-semilinear over $F$, that is $\varphi(f \cdot \omega) = \sigma(f)\,\varphi(\omega)$ for all $f \in F$ and all $\omega \in \Omega_{F/K}$. The conclusion is that $\varphi$ equals `qExpansionDiffAlong σ`, the map defined to be a choice of such a $\varphi$ when one exists and $0$ otherwise. Thus any map with these two properties is unique and is the one named by the definition.
--
--   This is the uniqueness (and specification) statement for the choice-totalised map `qExpansionDiffAlong`, which attaches to a $q$-expansion embedding $\sigma$ of a function field the induced map on differentials sending $\mathrm{d}x$ to $q\,\frac{d}{dq}\sigma(x)$. It is the device by which values of this canonical map are computed: any independently constructed map with the defining properties may be substituted for it, and it is used in the identifications of `qExpansionDiffAlong` with concrete differential $q$-expansions and in the transport of those identifications along congruences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong.lean

import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) {φ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) : φ = qExpansionDiffAlong σ := by sorry
