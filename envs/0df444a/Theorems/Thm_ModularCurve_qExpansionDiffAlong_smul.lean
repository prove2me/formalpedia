-- Prove2me | Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
-- name    : ModularCurve.qExpansionDiffAlong_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/88c8463e-e9a8-50ef-ae58-438436782225
-- title:
--   Semilinearity of the q-expansion map on differentials
-- statement:
--   Let $K$ be a field, let $F$ and $L$ be fields equipped with $K$-algebra structures, let $\sigma : F \to L((q))$ be a $K$-algebra homomorphism into the field of formal Laurent series over $L$, let $f \in F$ and let $\omega \in \Omega_{F/K}$ be a Kähler differential. Here `qExpansionDiffAlong` $\sigma$ denotes the $K$-linear map $\Omega_{F/K} \to L((q))$ obtained by choice: if some $K$-linear $\varphi : \Omega_{F/K} \to L((q))$ satisfies both $\varphi(\mathrm{d}x) = \theta_L(\sigma x)$ for all $x \in F$ and $\varphi(g \cdot \eta) = \sigma(g)\,\varphi(\eta)$ for all $g \in F$, $\eta \in \Omega_{F/K}$, then one such $\varphi$ is selected; otherwise the map is the zero map. The assertion is that this map is $\sigma$-semilinear for the $F$-module structure on $\Omega_{F/K}$: $$\mathrm{qExpansionDiffAlong}\ \sigma\ (f \cdot \omega) = \sigma(f)\cdot \mathrm{qExpansionDiffAlong}\ \sigma\ \omega,$$ the product being taken in $L((q))$. The identity holds with no existence hypothesis, since the zero map satisfies it as well.
--
--   This is the second clause of the defining property of the $q$-expansion map on differentials, read off from the choice-totalised definition; together with the companion identity on exact differentials $\mathrm{d}x$ it determines the $q$-expansion of every differential $f\,\mathrm{d}x$ as $\sigma(f)\,\theta_L(\sigma x)$. It is the form in which the semilinearity is used by the later computations with $q$-expansions of differentials on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpansionDiffAlong_smul.lean

import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.qExpansionDiffAlong_smul {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) (f : F) (ω : Ω[F⁄K]) : qExpansionDiffAlong σ (f • ω) = σ f * qExpansionDiffAlong σ ω := by sorry
