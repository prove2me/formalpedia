-- Prove2me | Theorems.Thm_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd
-- name    : ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3e62a272-cfae-59e6-b7c9-516d9669026a
-- title:
--   Relative degree at least ℓ+1 for level Mℓ
-- statement:
--   Let $M$ be a positive integer, $H$ a subgroup of $(\mathbb{Z}/M\mathbb{Z})^{\times}$, and $\ell$ a prime with $\ell \nmid M$. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion of $\Gamma_0(M)$ of the preimage of $H$ under the homomorphism `gamma0Units M`. Two intermediate fields of `LaurentSeries ℚ` over $\mathbb{Q}$ are compared: [`ModularCurve.xHFunctionField M H`](def/ModularCurve_XH.html#L79), the field obtained by adjoining to $\mathbb{Q}$ the set `intFormRatiosC ℚ (CohCarrier.GammaH M H)` attached to $\Gamma_H(M)$, and [`ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)`](def/ModularCurve_XH.html#L84), obtained in the same way from the group $\Gamma_H(M) \sqcap \Gamma_0(M\ell)$. The assertion is the inequality of cardinals $\ell + 1 \le$ `IntermediateField.relrank` of the first field in the second, i.e. the rank over the first field of the second one relative to their intersection; no finiteness of this relative degree is presupposed.
--
--   This is the lower bound $[\,F(\Gamma_H(M)\cap\Gamma_0(M\ell)) : F(\Gamma_H(M))\,] \ge \ell + 1$ for the $q$-expansion function fields of the modular curves of level $\Gamma_H(M)$ and $\Gamma_H(M)\cap\Gamma_0(\ell)$, the classical degree of the forgetful map between these curves for $\ell \nmid M$. It feeds the computations [`ModularCurve.finrankAlong_heckeAlphaHBar`](thm.html#ModularCurve.finrankAlong_heckeAlphaHBar) and [`ModularCurve.finrankAlong_heckeAlphaOneBar`](thm.html#ModularCurve.finrankAlong_heckeAlphaOneBar), where the degree of the extension cut out by the Hecke operator at $\ell$ is pinned down.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    ((ℓ + 1 : ℕ) : Cardinal) ≤
      IntermediateField.relrank (ModularCurve.xHFunctionField M H)
        (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := by sorry
