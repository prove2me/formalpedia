-- Prove2me | Theorems.Thm_ModularCurve_card_orbit_mul_jWidth
-- name    : ModularCurve.card_orbit_mul_jWidth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/a7bd8644-026e-5251-b559-c044ccdbefc8
-- title:
--   Anharmonic orbit size times j-width equals 6
-- statement:
--   Let $K$ be a field with decidable equality in which $2 \neq 0$ and $3 \neq 0$, and let $t \in K$ satisfy $t \neq 0$ and $t \neq 1$. Consider the finite subset of $K$ consisting of the six expressions $t$, $1-t$, $t^{-1}$, $1-t^{-1}$, $(1-t)^{-1}$ and $1-(1-t)^{-1}$ (a `Finset` built from this list, so that repetitions are collapsed), and let $j = \mathrm{legendreJ}(t) = 2^{8}(t^{2}-t+1)^{3}/\bigl(t^{2}(t-1)^{2}\bigr)$. Let $\mathrm{jWidth}(j)$ be $3$ if $j = 0$, $2$ if $j = 1728$, and $1$ otherwise. The assertion is the identity
--   $$\#\{t,\,1-t,\,t^{-1},\,1-t^{-1},\,(1-t)^{-1},\,1-(1-t)^{-1}\}\cdot \mathrm{jWidth}\bigl(\mathrm{legendreJ}(t)\bigr) = 6$$
--   in $\mathbb{N}$. Thus the displayed set has exactly $6$, $3$ or $2$ elements according as the width of $j$ at $\mathrm{legendreJ}(t)$ is $1$, $2$ or $3$.
--
--   This is the orbit–stabiliser count for the action of the anharmonic group of order $6$ on $K \setminus \{0,1\}$, weighted by the automorphism width $e(j)$: the orbit of $t$ has full size $6$ except over $j = 1728$ (orbit $\{-1,2,2^{-1}\}$, width $2$) and over $j = 0$ (orbit of the primitive sixth roots of unity, width $3$), the hypotheses $2 \neq 0$ and $3 \neq 0$ being what separates these cases. It is used in the fibrewise count behind [`ModularCurve.sum_inv_jWidth_of_deuringPolynomial`](thm.html#ModularCurve.sum_inv_jWidth_of_deuringPolynomial), where the weights $1/e(j)$ of the Eichler–Deuring mass formula are summed over Legendre parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_orbit_mul_jWidth.lean

import Mathlib
import Definitions.Def_ModularCurve_LegendreJ
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.card_orbit_mul_jWidth {K : Type*} [Field K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ({t, 1 - t, t⁻¹, 1 - t⁻¹, (1 - t)⁻¹, 1 - (1 - t)⁻¹} : Finset K).card * jWidth (legendreJ t)
      = 6 := by sorry
