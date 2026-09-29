-- Prove2me | Theorems.Thm_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D
-- name    : ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/7ee14a32-9e33-5053-a66d-01c044f51627
-- title:
--   q-expansion of the trace of a pulled-back differential
-- statement:
--   Let $K$, $F$, $F'$, $L$ be fields, with $F$ and $F'$ extensions of $K$, $F'$ an $F$-algebra compatibly with $K$, and $L$ a $K$-algebra. Let $\sigma_0 : F \to L((q))$ be a $K$-algebra map and $\varphi_0 : \Omega_{F/K} \to L((q))$ a $K$-linear map such that the pair satisfies `IsQExpansionDiffAlong`, i.e. $\varphi_0(d_{F/K}x) = \theta(\sigma_0 x)$ for all $x \in F$, where $\theta(g) = q\,g'$ is multiplication by the Laurent monomial $q$ composed with the formal derivative, and $\varphi_0(f \cdot \omega) = \sigma_0(f)\,\varphi_0(\omega)$ for $f \in F$, $\omega \in \Omega_{F/K}$. Let $t : \Omega_{F'/K} \to \Omega_{F/K}$ be $F$-linear and satisfy `IsTraceDiff`, i.e. $t\bigl(y \cdot \omega_{F'}\bigr) = \mathrm{Tr}_{F'/F}(y)\cdot \omega$ whenever $\omega_{F'}$ is the image of $\omega \in \Omega_{F/K}$ under the canonical map $\Omega_{F/K} \to \Omega_{F'/K}$, for all $y \in F'$. Let $\beta : F \to F'$ be a $K$-algebra map, $x \in F$, $h \in F'$ with $d_{F'/K}(\beta x) = h \cdot d_{F/K}x$ in $\Omega_{F'/K}$ (the differential of $x$ pushed forward along the structural $F$-algebra map). Then for every $f \in F$, $$\varphi_0\bigl(t(\beta^{*}(f\,d_{F/K}x))\bigr) = \sigma_0\bigl(\mathrm{Tr}_{F'/F}(\beta(f)\,h)\bigr)\cdot \theta(\sigma_0 x),$$ where $\beta^{*} =$ `pullbackDiff` $\beta$ is the $K$-linear map on differentials induced by $\beta$ (which need not coincide with the structural $F$-algebra map).
--
--   This is the generic form of the $q$-expansion computation for the operator $t \circ \beta^{*}$ on differentials: it reduces the $q$-expansion of the trace of a pulled-back differential $f\,dx$ to the $q$-expansion of the single function $\mathrm{Tr}_{F'/F}(\beta(f)h)$, times $\theta(\sigma_0 x)$. It is applied to the degeneracy and Hecke maps of modular function fields in [`ModularCurve.qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self`](thm.html#ModularCurve.qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self) and in the two coefficient computations [`ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC`](thm.html#ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC) and [`ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd`](thm.html#ModularCurve.coeff_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeAlphaC_of_dvd), which feed the weight-two formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansionDiff_traceDiff_pullbackDiff_smul_D.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.qExpansionDiff_traceDiff_pullbackDiff_smul_D {K F F' L : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Field L] [Algebra K L] {σ₀ : F →ₐ[K] LaurentSeries L} {φ₀ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ₀ : IsQExpansionDiffAlong σ₀ φ₀) {t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (ht : IsTraceDiff K F F' t) (β : F →ₐ[K] F') {x : F} {h : F'} (hD : KaehlerDifferential.D K F' (β x) = h • KaehlerDifferential.map K K F F' (KaehlerDifferential.D K F x)) (f : F) : φ₀ (t (pullbackDiff β (f • KaehlerDifferential.D K F x))) = σ₀ (Algebra.trace F F' (β f * h)) * thetaL L (σ₀ x) := by sorry
